open Bindlib
open Format
open Names

type t =
  (* functional *)
  | Var of t var
  | Ann of t * t
  | Type
  | Linear
  | TyProd of t * tbinder
  | LnProd of t * tbinder
  | Lambda of pbinder
  | Fix    of tbinder
  | App    of t * t
  | LetIn  of t * pbinder
  (* data *)
  | TCons  of Id.t * t list
  | DCons  of Id.t * t list
  | Match  of t * motive option 
                * pbinder list
  | Axiom  of Id.t * t
and p = 
  | PVar    of t var
  | PDCons  of Id.t * p list
  | PTCons  of Id.t * p list
and p0 =
  | P0Rel
  | P0TCons of Id.t * p0 list
  | P0DCons of Id.t * p0 list
and pbinder = p0 * (t, t) mbinder
and tbinder = (t, t) binder
and motive = (t, pbinder) binder

type tcons = 
  TConstr of Id.t * tscope * dcons list
and dcons = 
  DConstr of Id.t * tscope 
and tscope = 
  | Base of t
  | Bind of t * tsbinder
and tsbinder = (t, tscope) binder

type top =
  | Empty
  | Define of t * tpbinder
  | Datype of tcons * top
and tpbinder = (t, top) binder


let rec equal_p0 p1 p2 =
  match p1, p2 with
  | P0Rel, P0Rel -> true
  | P0TCons (id1, ps1), P0TCons (id2, ps2) -> (
    try
      Id.equal id1 id2 && List.fold_left2 
        (fun acc p1 p2 -> acc && equal_p0 p1 p2) true ps1 ps2
    with _ -> false)
  | P0DCons (id1, ps1), P0DCons (id2, ps2) -> (
    try
      Id.equal id1 id2 && List.fold_left2 
        (fun acc p1 p2 -> acc && equal_p0 p1 p2) true ps1 ps2
    with _ -> false)
  | _ -> false

let rec mt_of_pt0 p0 t =
  match p0, t with
  | P0Rel, _ -> [| t |]
  | P0TCons (_, ps), TCons (_, ts) ->
    List.fold_left2 
      (fun acc p t -> Array.append acc (mt_of_pt0 p t)) [| |] ps ts
  | P0DCons (_, ps), DCons (_, ts) ->
    List.fold_left2 
      (fun acc p t -> Array.append acc (mt_of_pt0 p t)) [| |] ps ts
  | _ -> failwith "mt_of_pt0"

let rec mvar_of_p = function
  | PVar x -> (P0Rel, [| x |])
  | PTCons (id, ps) ->
    let ps0, m =
      List.fold_left
        (fun (ps0, acc) p -> 
          let p0, m = mvar_of_p p in
          (p0 :: ps0, Array.append acc m)) 
        ([], [| |]) ps
    in
    (P0TCons (id, List.rev ps0), m)
  | PDCons (id, ps) ->
    let ps0, m =
      List.fold_left
        (fun (ps0, acc) p -> 
          let p0, m = mvar_of_p p in
          (p0 :: ps0, Array.append acc m)) 
        ([], [| |]) ps
    in
    (P0DCons (id, List.rev ps0), m)

let rec p_of_mvar p0 m =
  match p0 with
  | P0Rel ->
    let x = m.(0) in
    let m = Array.sub m 1 ((Array.length m) - 1) in
    (PVar x, m)
  | P0TCons (id, ps) ->
    let ps, m =
      List.fold_left
        (fun (ps, m) p0 ->
          let p, m = p_of_mvar p0 m in
          (p :: ps, m))
        ([], m) ps
    in
    (PTCons (id, List.rev ps), m)
  | P0DCons (id, ps) ->
    let ps, m =
      List.fold_left
        (fun (ps, m) p0 ->
          let p, m = p_of_mvar p0 m in
          (p :: ps, m))
        ([], m) ps
    in
    (PDCons (id, List.rev ps), m)

let bind_p p tb =
  let p0, m = mvar_of_p p in
  let mb = bind_mvar m tb in
  box_apply (fun mb -> (p0, mb)) mb

let unbind_p pb =
  let p0, mb = pb in
  let m, t = unmbind mb in
  let p, _ = p_of_mvar p0 m in
  (p, t)

let subst_p pb t =
  let p0, mb = pb in
  let m = mt_of_pt0 p0 t in
  msubst mb m

let box_binder_p f pb =
  let p0, mb = pb in
  let mb = box_mbinder f mb in
  box_apply (fun mb -> (p0, mb)) mb

let eq_binder_p f pb1 pb2 =
  let p1, mb1 = pb1 in
  let p2, mb2 = pb2 in
  equal_p0 p1 p2 && eq_mbinder f mb1 mb2

let mk = new_var (fun x -> Var x)
let __ = mk "_"

let _Var = box_var
let _Ann = box_apply2 (fun t ty -> Ann (t, ty))
let _Type = box Type
let _Linear = box Linear
let _TyProd = box_apply2 (fun ty b -> TyProd (ty, b))
let _LnProd = box_apply2 (fun ty b -> LnProd (ty, b))
let _Arrow ty1 ty2 = _TyProd ty1 (bind_var __ ty2)
let _Lolli ty1 ty2 = _LnProd ty1 (bind_var __ ty2)
let _Lambda = box_apply (fun pb -> Lambda pb)
let _Fix = box_apply (fun b -> Fix b)
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))
let _LetIn = box_apply2 (fun t pb -> LetIn (t, pb))
let _TCons id = box_apply (fun ts -> TCons (id, ts))
let _DCons id = box_apply (fun ts -> DCons (id, ts))
let _Match = box_apply3 (fun t p ps -> Match (t, p, ps))
let _Axiom id = box_apply (fun t -> Axiom (id, t))

let _TConstr id = box_apply2 (fun ts dc -> TConstr (id, ts, dc))
let _DConstr id = box_apply (fun ts -> DConstr (id, ts))

let _Base = box_apply (fun t -> Base t)
let _Bind = box_apply2 (fun t b -> Bind (t, b))
let _Bnd ty1 ty2 = _Bind ty1 (bind_var __ ty2)

let _DConstr id = box_apply (fun ts -> DConstr (id, ts))

let _Empty = box Empty
let _Define = box_apply2 (fun t tp -> Define (t, tp))
let _Datype = box_apply2 (fun tc t -> Datype (tc, t))

let _None = box None
let _Some x = box_apply (fun x -> Some x) x
let box_opt f = function
  | None -> box None
  | Some t -> 
    box_apply (fun t -> Some t) (f t)

let _nil = box []
let _cons t ts = box_apply2 (fun t ts -> t :: ts) t ts
let box_of_list xs =
  List.fold_right (fun x acc -> _cons x acc) xs _nil
let rec box_map f = function
  | [] -> box []
  | x :: xs -> 
    box_apply2 (fun x xs -> x :: xs) (f x) (box_map f xs)

let rec lift = function
  | Var x -> _Var x
  | Ann (t, ty) -> _Ann (lift t) (lift ty)
  | Type -> _Type
  | Linear -> _Linear
  | TyProd (ty, b) -> _TyProd (lift ty) (box_binder lift b)
  | LnProd (ty, b) -> _LnProd (lift ty) (box_binder lift b)
  | Lambda pb -> _Lambda (box_binder_p lift pb)
  | Fix b -> _Fix (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)
  | LetIn (t, pb) -> _LetIn (lift t) (box_binder_p lift pb)
  | TCons (id, ts) -> _TCons id (box_map lift ts)
  | DCons (id, ts) -> _DCons id (box_map lift ts)
  | Match (t, opt, pbs) ->
    _Match (lift t) (box_opt (box_binder (box_binder_p lift)) opt) 
                    (box_map (box_binder_p lift) pbs)
  | Axiom (id, t) -> _Axiom id (lift t)


let rec pp_p fmt = function
  | PVar x -> fprintf fmt "%s_%d" (name_of x) (uid_of x)
  | PTCons (id, ps) ->
    fprintf fmt ""
  

(* let rec spine t = 
  match t with
  | Lambda b ->
    let x, b = unbind_p b in
    let xs, t = spine b in
    (x :: xs, t)
  | _ -> ([], t)

let rec pp fmt t = 
  let pp_aux fmt =
    List.iter (fun x -> 
      Format.fprintf fmt "%s " (name_of x))
  in
  match t with
  | Var x -> 
    Format.fprintf fmt "%s" (name_of x)
  | Ann (s, t) -> 
    Format.fprintf fmt "@[(%a :@;<1 2>%a)@]" pp s pp t
  | Type -> Format.fprintf fmt "Type"
  | Linear -> Format.fprintf fmt "Linear"
  | TyProd (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then Format.fprintf fmt "@[%a ->@;<1 2>%a@]" pp ty pp b
    else Format.fprintf fmt "@[@[(%s :@;<1 2>%a) ->@]@;<1 2>%a@]"
      (name_of x) pp ty pp b
  | LnProd (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then Format.fprintf fmt "@[%a >>@;<1 2>%a@]" pp ty pp b
    else Format.fprintf fmt "@[@[(%s :@;<1 2>%a) >>@]@;<1 2>%a@]"
      (name_of x) pp ty pp b
  | Lambda b ->
    let x, b = unbind b in
    let xs, b = spine b in
    Format.fprintf fmt "@[fun %s %a=>@;<1 2>%a@]"
      (name_of x) pp_aux xs pp b
  | App (s, t) ->
    Format.fprintf fmt "@[(%a)@;<1 2>%a@]" pp s pp t
  | LetIn (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[let %s :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x) pp t pp b
  | Eq (t1, t2, _) ->
    Format.fprintf fmt "@[Eq(%a,@;<1 2>%a)@]" pp t1 pp t2
  | Refl (t, ty) ->
    Format.fprintf fmt "@[refl(%a,@;<1 2> %a)@]" pp t pp ty
  | Ind (p, pf, t1, t2, eq, ty) ->
    Format.fprintf fmt 
      "@[ind(%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a)@]"
      pp p pp pf pp t1 pp t2 pp eq pp ty
  | Tensor (ty, b) ->
    let x, b = unbind b in
    if (name_of x = "_") then
      Format.fprintf fmt "@[(%a *@;<1 2>%a)@]" pp ty pp b
    else
      Format.fprintf fmt "@[(%s : %a *@;<1 2>%a)@]" (name_of x) pp ty pp b
  | Pair (t1, t2) ->
    Format.fprintf fmt "@[(%a, %a)@]" pp t1 pp t2
  | LetPair (t, mb) ->
    let x, mb = unmbind mb in
    let x1 = x.(0) in
    let x2 = x.(1) in
    Format.fprintf fmt "@[@[let (%s, %s) :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x1) (name_of x2) pp t pp mb
  | CoProd (ty1, ty2) ->
    Format.fprintf fmt "@[(%a |@;<1 2>%a)@]" pp ty1 pp ty2
  | InjL t -> 
    Format.fprintf fmt "@[(left %a)@]" pp t
  | InjR t -> 
    Format.fprintf fmt "@[(right %a)@]" pp t
  | Case (t, b1, b2) ->
    let x1, b1 = unbind b1 in
    let x2, b2 = unbind b2 in
    Format.fprintf fmt "@[case %a of@;<1; 0> %s => %a@;<1; 0>|%s => %a]"
      pp t (name_of x1) pp b1 (name_of x2) pp b2
  | Unit -> Format.fprintf fmt "@[Unit@]"
  | U -> Format.fprintf fmt "()"
  | Nat -> Format.fprintf fmt "Nat"
  | Zero -> Format.fprintf fmt "0"
  | Succ t -> 
    let rec loop i = function
      | Succ t -> loop (i + 1) t
      | Zero -> Format.fprintf fmt "%d" i
      | t -> Format.fprintf fmt "(%a +1)" pp t
    in
    loop 1 t
  | Iter (p, t1, t2, n) ->
    Format.fprintf fmt 
      "@[iter(%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a)@]"
      pp p pp t1 pp t2 pp n
  | PtsTo (t, ty) -> 
    Format.fprintf fmt "@[[%a |->@;<1 2>%a]@]" pp t pp ty
  | Alloc -> Format.fprintf fmt "alloc"
  | Free -> Format.fprintf fmt "free"
  | Get -> Format.fprintf fmt "get"
  | Set -> Format.fprintf fmt "set" *)
