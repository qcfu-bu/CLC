open Bindlib
open Terms
open Equality

let rec eval t =
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
    TyProd (ty, b)
  | Lambda b -> 
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (eval b))) in
    Lambda b
  | App (t1, t2) -> (
    let t1 = eval t1 in
    match t1 with
    | Lambda b ->
      let t2 = eval t2 in
      eval (subst b t2)
    | _ -> App (t1, eval t2))
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
  | Channel -> t
  | Open -> t
  | Close -> t
  | Read -> t
  | Write -> t
  | PtsTo _ -> t
  | Ptr _ -> t
  | Alloc -> t
  | Free -> t
  | Get -> t
  | Set -> t
