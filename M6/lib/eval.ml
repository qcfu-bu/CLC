open Bindlib
open Terms
open Equality
open Format

module Heap : sig
  type loc = int
  type heap
  val heap : heap
  val alloc : t -> loc
  val free : loc -> unit
  val get : loc -> t
  val set : loc -> t -> unit
  val pp : formatter -> heap -> unit
end =
struct
  type loc = int
  type heap = t option array
  let heap : heap = Array.make 4096 None
  let stack = ref (List.init 4096 (fun x -> x))

  let alloc t =  
    match !stack with
    | [] -> failwith "memory exhausted"
    | x :: xs ->
      heap.(x) <- Some t;
      stack := xs;
      x

  let free l =
    heap.(l) <- None;
    stack := l :: !stack

  let get l =
    match heap.(l) with
    | Some t -> t
    | None -> failwith "cannot access memory location"

  let set l t =
    heap.(l) <- Some t

  let pp fmt h =
    let pp_aux fmt h =
      Array.iteri (fun l ty_opt -> 
        match ty_opt with
        | Some ty ->
          fprintf fmt "@[<v 0>@;<0 2>@[%d :=@;<1 2>%a@]@]@?" 
            l Terms.pp ty
        | _ -> ()) h
    in
  fprintf fmt "@[<hv>[@?@[%a@;<1 0>@]]@]@?" pp_aux h
end

let rec nat_of_int n =
  if n <= 0 
  then Zero
  else Succ (nat_of_int (n - 1))

let rec int_of_nat t =
  match t with
  | Zero -> 0
  | Succ t -> 1 + (int_of_nat t)
  | _ -> failwith (asprintf "non-nat value(%a)" Terms.pp t)

let rec spine t =
  match t with
  | App (t1, t2) -> spine t1 @ [t2]
  | _ -> [t]

and eval t =
  match t with
  | Var _ -> t
  | Ann (t, _) -> eval t
  | Type -> t
  | Linear -> t
  | TyProd (ty, b) -> 
    let x, b = unbind b in
    let ty = eval ty in
    let b = unbox (bind_var x (lift (eval b))) in
    TyProd (ty, b)
  | LnProd (ty, b) ->
    let x, b = unbind b in
    let ty = eval ty in
    let b = unbox (bind_var x (lift (eval b))) in
    LnProd (ty, b)
  | Lambda _ -> t
  | App (t1, t2) -> (
    let t1 = eval t1 in
    let t2 = eval t2 in
    match t1 with
    | Lambda b ->
      eval (subst b t2)
    | _ -> (
      let sp = spine t1 in
      match sp with
      | [ Alloc; _ ] ->
        let l = Heap.alloc t2 in
        Pair (nat_of_int l, U)
      | [ Free; _; l ] ->
        Heap.free (int_of_nat l); U
      | [ Get; _; l ] ->
        let t = Heap.get (int_of_nat l) in
        Pair (t, U)
      | [ Set; _; _; l; _ ] ->
        Heap.set (int_of_nat l) t2; U
      | _ -> App (t1, t2)))
  | LetIn (t, b) ->
    let t = eval t in
    eval (subst b t)
  | Eq (t1, t2, ty) -> Eq (eval t1, eval t2, eval ty)
  | Refl (t, ty) -> Refl (eval t, eval ty)
  | Ind (p, pf, t1, t2, eq, ty) -> (
    let p = eval p in
    let pf = eval pf in
    let t1 = eval t1 in
    let t2 = eval t2 in
    let eq = eval eq in
    let ty = eval ty in
    match eq with
    | Refl (t3, eq_ty) ->
      if (equal t1 t3 && equal t2 t3 && equal ty eq_ty)
      then eval (App (pf, t3))
      else Ind (p, pf, t1, t2, eq, ty)
    | _ -> Ind (p, pf, t1, t2, eq, ty))
  | Tensor (ty, b) -> 
    let x, b = unbind b in
    let ty = eval ty in
    let b = unbox (bind_var x (lift (eval b))) in
    Tensor (ty, b)
  | Pair (t1, t2) ->
    let t1 = eval t1 in
    let t2 = eval t2 in
    Pair (t1, t2)
  | LetPair (t, mb) -> (
    let t = eval t in
    match t with
    | Pair (t1, t2) ->
      eval (msubst mb [| t1; t2 |])
    | _ -> 
      let occurs = mbinder_occurs mb in
      if Array.for_all (fun x -> not x) occurs then
        eval (snd (unmbind mb))
      else 
        let mx, mb = unmbind mb in
        let mb = unbox (bind_mvar mx (lift (eval mb))) in
        LetPair (t, mb))
  | CoProd (ty1, ty2) -> CoProd (eval ty1, eval ty2)
  | InjL t -> InjL (eval t)
  | InjR t -> InjR (eval t)
  | Case (t, b1, b2) -> (
    let t = eval t in
    match t with
    | InjL t -> eval (subst b1 t)
    | InjR t -> eval (subst b2 t)
    | _ -> Case (t, b1, b2))
  | Unit -> t
  | U -> t
  | Nat -> t
  | Zero -> t
  | Succ t -> Succ (eval t)
  | Iter (p, t1, t2, n) -> (
    let p = eval p in
    let t1 = eval t1 in
    let t2 = eval t2 in
    let n = eval n in
    match n with
    | Zero -> eval t1
    | Succ n ->
      eval (App (App (t2, n), Iter (p, t1, t2, n)))
    | _ -> Iter (p, t1, t2, n))
  | PtsTo (t, ty) -> PtsTo (eval t, eval ty)
  | Alloc -> t
  | Free -> t
  | Get -> t
  | Set -> t
