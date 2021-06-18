open Bindlib
open Format
open Rig
open Names

type t =
  (* functional *)
  | Var of t var
  | Ann of t * t
  | Type
  | Linear
  | TyProd of t * tbinder
  | LnProd of t * tbinder
  | Lambda of tbinder
  | Fix    of tbinder
  | App    of t * t
  | LetIn  of t * tbinder
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
  TConstr of Id.t * pscope * dcons list
and dcons = 
  DConstr of Id.t * pscope 
and pscope =
  | PBase of tscope
  | PBind of t * psbinder
and psbinder = (t, pscope) binder
and tscope = 
  | TBase of t
  | TBind of t * tsbinder
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

and pp_p0 fmt = function
  | P0Rel -> fprintf fmt "P0Rel"
  | P0TCons (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps0 ps
  | P0DCons (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps0 ps

and pp_ps0 fmt = function
  | p :: [] -> fprintf fmt "%a" pp_p0 p
  | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p0 p pp_ps0 ps
  | _ -> ()

and mt_of_pt0 p0 t =
  match p0, t with
  | P0Rel, _ -> [| t |]
  | P0TCons (id1, ps), TCons (id2, ts) ->
    if Id.equal id1 id2 then
      List.fold_left2 
        (fun acc p t -> Array.append acc (mt_of_pt0 p t)) [| |] ps ts
    else failwith (asprintf "mt_of_pt0(%a;@;<1 2>%a)@." pp_p0 p0 pp t)
  | P0DCons (id1, ps), DCons (id2, ts) ->
    if Id.equal id1 id2 then
      List.fold_left2 
        (fun acc p t -> Array.append acc (mt_of_pt0 p t)) [| |] ps ts
    else failwith (asprintf "mt_of_pt0(%a;@;<1 2>%a)@." pp_p0 p0 pp t)
  | _ -> failwith (asprintf "mt_of_pt0(%a;@;<1 2>%a)@." pp_p0 p0 pp t)

and mvar_of_p = function
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

and p_of_mvar p0 m =
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

and bind_p p tb =
  let p0, m = mvar_of_p p in
  let mb = bind_mvar m tb in
  box_apply (fun mb -> (p0, mb)) mb

and unbind_p pb =
  let p0, mb = pb in
  let m, t = unmbind mb in
  let p, _ = p_of_mvar p0 m in
  (p, t)

and subst_p pb t =
  let p0, mb = pb in
  let m = mt_of_pt0 p0 t in
  let t = msubst mb m in
  t

and box_binder_p f pb =
  let p0, mb = pb in
  let mb = box_mbinder f mb in
  box_apply (fun mb -> (p0, mb)) mb

and eq_binder_p f pb1 pb2 =
  let p1, mb1 = pb1 in
  let p2, mb2 = pb2 in
  equal_p0 p1 p2 && eq_mbinder f mb1 mb2

and pp_v fmt x = fprintf fmt "%s_%d" (name_of x) (uid_of x)

and pp_p fmt = function
  | PVar x -> fprintf fmt "%a" pp_v x
  | PTCons (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps
  | PDCons (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps

and pp_ps fmt = function
  | p :: [] -> fprintf fmt "%a" pp_p p
  | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p p pp_ps ps
  | _ -> ()

and spine t = 
  match t with
  | Lambda b ->
    let x, b = unbind b in
    let xs, t = spine b in
    (x :: xs, t)
  | _ -> ([], t)

and pp fmt t = 
  let pp_aux fmt =
    List.iter (fun x -> 
      fprintf fmt "%a " pp_v x)
  in
  match t with
  | Var x -> 
    fprintf fmt "%a" pp_v x
  | Ann (s, t) -> 
    fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp s pp t
  | Type -> fprintf fmt "Type"
  | Linear -> fprintf fmt "Linear"
  | TyProd (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then fprintf fmt "@[%a ->@;<1 2>%a@]" pp ty pp b
    else fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]"
      pp_v x pp ty pp b
  | LnProd (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then fprintf fmt "@[%a >>@;<1 2>%a@]" pp ty pp b
    else fprintf fmt "@[@[(%a :@;<1 2>%a) >>@]@;<1 2>%a@]"
      pp_v x pp ty pp b
  | Lambda b ->
    let x, b = unbind b in
    let ps, b = spine b in
    fprintf fmt "@[fun %a %a=>@;<1 2>%a@]"
      pp_v x pp_aux ps pp b
  | Fix b ->
    let x, b = unbind b in
    let ps, b = spine b in
    fprintf fmt "@[fix %a %a=>@;<1 2>%a@]"
      pp_v x pp_aux ps pp b
  | App (s, t) ->
    fprintf fmt "@[(%a)@;<1 2>%a@]" pp s pp t
  | LetIn (t, b) -> 
    let x, b = unbind b in
    fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      pp_v x pp t pp b
  | TCons (id, ts) -> (
    match ts with
    | [] -> fprintf fmt "%a" Id.pp id
    | _ -> 
      fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ts)
  | DCons (id, ts) -> (
    match ts with
    | [] -> fprintf fmt "%a" Id.pp id
    | _ -> fprintf fmt "@[(%a %a)@]" Id.pp id pp_ts ts)
  | Match (t, mt, cls) ->
    fprintf fmt "@[<v 0>@[match %a%a@;<1 0>with@]@;<1 0>@[%a@]end@]"
      pp t pp_mt mt pp_cls cls
  | Axiom (id, _) ->
    fprintf fmt "%a" Id.pp id

and pp_ts fmt = function
  | t :: [] -> fprintf fmt "%a" pp t
  | t :: ts -> fprintf fmt "@[%a@;<1 2>%a@]" pp t pp_ts ts
  | _ -> ()

and pp_mt fmt = function
  | Some mt ->
    let x, pb = unbind mt in
    let p, b = unbind_p pb in
    if (name_of x = "_")
    then fprintf fmt " in %a return@;<1 2>%a" pp_p p pp b
    else fprintf fmt " as %a in %a return@;<1 2>%a" pp_v x pp_p p pp b
  | None -> ()

and pp_cl fmt pb =
  let p, t = unbind_p pb in
  fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp t

and pp_cls fmt = function
  | cl :: cls ->
    fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls
  | _ -> ()

let rec pp_top fmt = function
  | Empty -> ()
  | Define (t, tp) -> (
    match t with
    | Axiom (_, ty) ->
      let x, tp = unbind tp in
      fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" 
        pp_v x pp ty pp_top tp
    | _ ->
      let x, tp = unbind tp in
      fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" 
        pp_v x pp t pp_top tp)
  | Datype (dcs, tp) ->
    let TConstr (id, ts, cs) = dcs in
    fprintf fmt "@[Inductive %a %a :=@.%a@.@.%a@]" 
      Id.pp id pp_pscope ts pp_dcons cs pp_top tp

and pp_pscope fmt = function
  | PBase t -> fprintf fmt ": %a" pp_tscope t
  | PBind (ty, b) ->
    let x, b = unbind b in
    if (name_of x = "_") 
    then fprintf fmt "@[%a@;<1 2>%a@]" pp ty pp_pscope b
    else fprintf fmt "@[@[(%a :@;<1 2>%a)@]@;<1 2>%a@]"
      pp_v x pp ty pp_pscope b
    
and pp_tscope fmt = function
  | TBase t -> fprintf fmt "%a" pp t
  | TBind (ty, b) ->
    let x, b = unbind b in
    if (name_of x = "_") 
    then fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp ty pp_tscope b
    else fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]"
      pp_v x pp ty pp_tscope b

and pp_dcons fmt = function
  | c :: [] ->
    let DConstr (id, ts) = c in
    fprintf fmt "@[| %a %a.@]" 
      Id.pp id pp_pscope ts
  | c :: cs ->
    let DConstr (id, ts) = c in
    fprintf fmt "@[<v 0>| %a %a@;<1 0>%a@]" 
      Id.pp id pp_pscope ts pp_dcons cs
  | _ -> ()


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

let _PBase = box_apply (fun t -> PBase t)
let _PBind = box_apply2 (fun t b -> PBind (t, b))
let _PBnd ty1 ty2 = _PBind ty1 (bind_var __ ty2)
let _TBase = box_apply (fun t -> TBase t)
let _TBind = box_apply2 (fun t b -> TBind (t, b))
let _TBnd ty1 ty2 = _TBind ty1 (bind_var __ ty2)

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
  | Lambda pb -> _Lambda (box_binder lift pb)
  | Fix b -> _Fix (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)
  | LetIn (t, pb) -> _LetIn (lift t) (box_binder lift pb)
  | TCons (id, ts) -> _TCons id (box_map lift ts) 
  | DCons (id, ts) -> _DCons id (box_map lift ts)
  | Match (t, opt, pbs) ->
    _Match (lift t) (box_opt (box_binder (box_binder_p lift)) opt) 
                    (box_map (box_binder_p lift) pbs)
  | Axiom (id, t) -> _Axiom id (lift t)
