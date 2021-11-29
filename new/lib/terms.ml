open Bindlib
open Names
open Format

type sort =
  | U
  | L

(* types *)
type ty = t

(* terms *)
and t =
  (* inference *)
  | Meta of Meta.t
  | Ann of t * ty
  (* functional *)
  | Var of t var
  | Sort of sort
  | Arrow of ty * tbinder
  | Lolli of ty * tbinder
  | Lambda of tbinder
  | App of t * t
  | LetIn of t * tbinder
  (* inductive *)
  | Ind of Id.t * t list
  | Constr of Id.t * t list
  | Match of t * mot * pbinder list
  | Fix of tbinder
  | Axiom of Id.t * ty

(* bound patterns *)
and p =
  | PVar of t var
  | PInd of Id.t * p list
  | PConstr of Id.t * p list

(* free patterns *)
and p0 =
  | P0Rel
  | P0Ind of Id.t * p0 list
  | P0Constr of Id.t * p0 list

(* motive *)
and mot =
  | Mot0
  | Mot1 of pbinder
  | Mot2 of (t, pbinder) binder

(* variable binder *)
and tbinder = (t, t) binder

(* pattern binder *)
and pbinder = p0 * (t, t) mbinder

(* inductive definition *)
type ind =
  { id : Id.t
  ; ty : pscope
  ; cs : constr list
  }

(* constructor defintion *)
and constr =
  { id : Id.t
  ; ty : pscope
  }

(* parameter scope *)
and pscope =
  | PBase of tscope
  | PBind of ty * psbinder

(* telescope *)
and tscope =
  | TBase of ty
  | TBind of ty * tsbinder

and psbinder = (t, pscope) binder

and tsbinder = (t, tscope) binder

(* top level definitions *)
type top =
  | Main of t
  | Define of t * tpbinder
  | Datype of ind * top

and tpbinder = (t, top) binder

exception PBacktrack of string

let rec equal_p0 p1 p2 =
  match (p1, p2) with
  | P0Rel, P0Rel -> true
  | P0Ind (id1, ps1), P0Ind (id2, ps2) -> (
    try
      Id.equal id1 id2
      && List.fold_left2 (fun acc p1 p2 -> acc && equal_p0 p1 p2) true ps1 ps2
    with
    | _ -> false)
  | P0Constr (id1, ps1), P0Constr (id2, ps2) -> (
    try
      Id.equal id1 id2
      && List.fold_left2 (fun acc p1 p2 -> acc && equal_p0 p1 p2) true ps1 ps2
    with
    | _ -> false)
  | _ -> false

and pp_p0 fmt = function
  | P0Rel -> fprintf fmt "P0Rel"
  | P0Ind (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps0 ps
  | P0Constr (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps0 ps

and pp_ps0 fmt = function
  | [ p ] -> fprintf fmt "%a" pp_p0 p
  | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p0 p pp_ps0 ps
  | _ -> ()

and mt_of_pt0 p0 t =
  match (p0, t) with
  | P0Rel, _ -> [| t |]
  | P0Ind (id1, ps), Ind (id2, ts) ->
    if Id.equal id1 id2 then
      List.fold_left2
        (fun acc p t -> Array.append acc (mt_of_pt0 p t))
        [||] ps ts
    else
      raise (PBacktrack (asprintf "mt_of_pt0(%a;@;<1 2>%a)@." pp_p0 p0 pp t))
  | P0Constr (id1, ps), Constr (id2, ts) ->
    if Id.equal id1 id2 then
      List.fold_left2
        (fun acc p t -> Array.append acc (mt_of_pt0 p t))
        [||] ps ts
    else
      raise (PBacktrack (asprintf "mt_of_pt0(%a;@;<1 2>%a)@." pp_p0 p0 pp t))
  | _ -> raise (PBacktrack (asprintf "mt_of_pt0(%a;@;<1 2>%a)@." pp_p0 p0 pp t))

and mvar_of_p = function
  | PVar x -> (P0Rel, [| x |])
  | PInd (id, ps) ->
    let ps0, m =
      List.fold_left
        (fun (ps0, acc) p ->
          let p0, m = mvar_of_p p in
          (p0 :: ps0, Array.append acc m))
        ([], [||])
        ps
    in
    (P0Ind (id, List.rev ps0), m)
  | PConstr (id, ps) ->
    let ps0, m =
      List.fold_left
        (fun (ps0, acc) p ->
          let p0, m = mvar_of_p p in
          (p0 :: ps0, Array.append acc m))
        ([], [||])
        ps
    in
    (P0Constr (id, List.rev ps0), m)

and list_of_p = function
  | PVar x -> [ x ]
  | PInd (_, ps) ->
    let xss = List.fold_right (fun p acc -> list_of_p p :: acc) ps [] in
    List.concat xss
  | PConstr (_, ps) ->
    let xss = List.fold_right (fun p acc -> list_of_p p :: acc) ps [] in
    List.concat xss

and p_of_mvar p0 m =
  match p0 with
  | P0Rel ->
    let x = m.(0) in
    let m = Array.sub m 1 (Array.length m - 1) in
    (PVar x, m)
  | P0Ind (id, ps) ->
    let ps, m =
      List.fold_left
        (fun (ps, m) p0 ->
          let p, m = p_of_mvar p0 m in
          (p :: ps, m))
        ([], m) ps
    in
    (PInd (id, List.rev ps), m)
  | P0Constr (id, ps) ->
    let ps, m =
      List.fold_left
        (fun (ps, m) p0 ->
          let p, m = p_of_mvar p0 m in
          (p :: ps, m))
        ([], m) ps
    in
    (PConstr (id, List.rev ps), m)

and bind_p p tb =
  let p0, m = mvar_of_p p in
  let mb = bind_mvar m tb in
  box_apply (fun mb -> (p0, mb)) mb

and unbind_p pb =
  let p0, mb = pb in
  let m, t = unmbind mb in
  let p, _ = p_of_mvar p0 m in
  (p, t)

and unbind_p2 pb1 pb2 =
  let p1, mb1 = pb1 in
  let p2, mb2 = pb2 in
  assert (equal_p0 p1 p2);
  let m, t1, t2 = unmbind2 mb1 mb2 in
  let p, _ = p_of_mvar p1 m in
  (p, t1, t2)

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
  | PInd (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps
  | PConstr (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps

and pp_ps fmt = function
  | [ p ] -> fprintf fmt "%a" pp_p p
  | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p p pp_ps ps
  | _ -> ()

and pp_s fmt t =
  match t with
  | U -> fprintf fmt "U"
  | L -> fprintf fmt "L"

and pp fmt t =
  let rec pp_aux fmt = List.iter (fun x -> fprintf fmt "%a " pp_v x)
  and spine t =
    match t with
    | Lambda b ->
      let x, b = unbind b in
      let xs, t = spine b in
      (x :: xs, t)
    | _ -> ([], t)
  in
  match t with
  | Var x -> fprintf fmt "%a" pp_v x
  | Meta x -> fprintf fmt "%a" Meta.pp x
  | Ann (s, t) -> fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp s pp t
  | Sort t -> fprintf fmt "%a" pp_s t
  | Arrow (ty, b) ->
    let x, b = unbind b in
    if name_of x = "_" then
      fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp ty pp b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]" pp_v x pp ty pp b
  | Lolli (ty, b) ->
    let x, b = unbind b in
    if name_of x = "_" then
      fprintf fmt "@[(%a) -o@;<1 2>%a@]" pp ty pp b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a) -o@]@;<1 2>%a@]" pp_v x pp ty pp b
  | Lambda b ->
    let x, b = unbind b in
    let ps, b = spine b in
    fprintf fmt "@[fun %a %a=>@;<1 2>%a@]" pp_v x pp_aux ps pp b
  | Fix b ->
    let x, b = unbind b in
    let ps, b = spine b in
    fprintf fmt "@[fix %a %a=>@;<1 2>%a@]" pp_v x pp_aux ps pp b
  | App (s, t) -> fprintf fmt "@[(%a)@;<1 2>%a@]" pp s pp t
  | LetIn (t, b) ->
    let x, b = unbind b in
    fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" pp_v x pp t pp b
  | Ind (id, ts) -> (
    match ts with
    | [] -> fprintf fmt "%a" Id.pp id
    | _ -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ts)
  | Constr (id, ts) -> (
    match ts with
    | [] -> fprintf fmt "%a" Id.pp id
    | _ -> fprintf fmt "@[(%a %a)@]" Id.pp id pp_ts ts)
  | Match (t, mt, cls) ->
    fprintf fmt "@[<v 0>@[match %a%a@;<1 0>with@]@;<1 0>@[%a@]end@]" pp t pp_mt
      mt pp_cls cls
  | Axiom (id, _) -> fprintf fmt "%a" Id.pp id

and pp_ts fmt = function
  | [ t ] -> fprintf fmt "%a" pp t
  | t :: ts -> fprintf fmt "@[%a@;<1 2>%a@]" pp t pp_ts ts
  | _ -> ()

and pp_mt fmt = function
  | Mot0 -> ()
  | Mot1 mt ->
    let p, b = unbind_p mt in
    fprintf fmt " in %a return@;<1 2>%a" pp_p p pp b
  | Mot2 mt ->
    let x, pb = unbind mt in
    let p, b = unbind_p pb in
    fprintf fmt " as %a in %a return@;<1 2>%a" pp_v x pp_p p pp b

and pp_cl fmt pb =
  let p, t = unbind_p pb in
  fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp t

and pp_cls fmt = function
  | cl :: cls -> fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls
  | _ -> ()

let rec pp_top fmt = function
  | Main t -> fprintf fmt "@[Definition main :=@;<1 2>%a.@]" pp t
  | Define (t, tp) -> (
    match t with
    | Axiom (_, ty) ->
      let x, tp = unbind tp in
      fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" pp_v x pp ty pp_top tp
    | _ ->
      let x, tp = unbind tp in
      fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" pp_v x pp t pp_top tp)
  | Datype (ind, tp) ->
    fprintf fmt "@[Inductive %a %a :=@.%a@.@.%a@]" Id.pp ind.id pp_pscope ind.ty
      pp_constr ind.cs pp_top tp

and pp_pscope fmt = function
  | PBase t -> fprintf fmt ": %a" pp_tscope t
  | PBind (ty, b) ->
    let x, b = unbind b in
    if name_of x = "_" then
      fprintf fmt "@[%a@;<1 2>%a@]" pp ty pp_pscope b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a)@]@;<1 2>%a@]" pp_v x pp ty pp_pscope b

and pp_tscope fmt = function
  | TBase t -> fprintf fmt "%a" pp t
  | TBind (ty, b) ->
    let x, b = unbind b in
    if name_of x = "_" then
      fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp ty pp_tscope b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]" pp_v x pp ty pp_tscope b

and pp_constr fmt = function
  | [ c ] -> fprintf fmt "@[| %a %a.@]" Id.pp c.id pp_pscope c.ty
  | c :: cs ->
    fprintf fmt "@[<v 0>| %a %a@;<1 0>%a@]" Id.pp c.id pp_pscope c.ty pp_constr
      cs
  | _ -> ()

let spine t =
  let rec spine_aux t sp =
    match t with
    | App (t1, t2) -> spine_aux t1 (t2 :: sp)
    | _ -> (t, sp)
  in
  spine_aux t []

let respine h sp = List.fold_left (fun acc t -> App (acc, t)) h sp

let mk = new_var (fun x -> Var x)

let blank = mk "_"

let _Var = box_var

let _Meta m = box (Meta m)

let _Ann = box_apply2 (fun t ty -> Ann (t, ty))

let _Sort t = box (Sort t)

let _U = box (Sort U)

let _L = box (Sort L)

let _Arrow = box_apply2 (fun ty b -> Arrow (ty, b))

let _Lolli = box_apply2 (fun ty b -> Lolli (ty, b))

let _Arrow0 ty1 ty2 = _Arrow ty1 (bind_var blank ty2)

let _Arrow1 tys ty = List.fold_right (fun ty acc -> _Arrow0 ty acc) tys ty

let _Lolli0 ty1 ty2 = _Lolli ty1 (bind_var blank ty2)

let _Lambda = box_apply (fun pb -> Lambda pb)

let _Lambda' xs ub =
  List.fold_right (fun x acc -> _Lambda (bind_var x acc)) xs ub

let _Fix = box_apply (fun b -> Fix b)

let _App = box_apply2 (fun t1 t2 -> App (t1, t2))

let _App' h sp = List.fold_left (fun acc x -> _App acc x) h sp

let _LetIn = box_apply2 (fun t pb -> LetIn (t, pb))

let _Ind id = box_apply (fun ts -> Ind (id, ts))

let _Constr id = box_apply (fun ts -> Constr (id, ts))

let _Match = box_apply3 (fun t p ps -> Match (t, p, ps))

let _Axiom id = box_apply (fun t -> Axiom (id, t))

let _Mot0 = box Mot0

let _Mot1 = box_apply (fun t -> Mot1 t)

let _Mot2 = box_apply (fun t -> Mot2 t)

let _ind id = box_apply2 (fun ty cs -> { id; ty; cs })

let _constr id = box_apply (fun ty -> { id; ty })

let _PBase = box_apply (fun t -> PBase t)

let _PBind = box_apply2 (fun t b -> PBind (t, b))

let _PBnd ty1 ty2 = _PBind ty1 (bind_var blank ty2)

let _TBase = box_apply (fun t -> TBase t)

let _TBind = box_apply2 (fun t b -> TBind (t, b))

let _TBnd ty1 ty2 = _TBind ty1 (bind_var blank ty2)

let _Main = box_apply (fun t -> Main t)

let _Define = box_apply2 (fun t tp -> Define (t, tp))

let _Datype = box_apply2 (fun tc t -> Datype (tc, t))

let _nil = box []

let _cons t ts = box_apply2 (fun t ts -> t :: ts) t ts

let box_of_list xs = List.fold_right (fun x acc -> _cons x acc) xs _nil

let rec box_map f = function
  | [] -> box []
  | x :: xs -> box_apply2 (fun x xs -> x :: xs) (f x) (box_map f xs)

let rec lift t =
  match t with
  | Var x -> _Var x
  | Meta x -> _Meta x
  | Ann (t, ty) -> _Ann (lift t) (lift ty)
  | Sort t -> _Sort t
  | Arrow (ty, b) -> _Arrow (lift ty) (box_binder lift b)
  | Lolli (ty, b) -> _Lolli (lift ty) (box_binder lift b)
  | Lambda b -> _Lambda (box_binder lift b)
  | Fix b -> _Fix (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)
  | LetIn (t, b) -> _LetIn (lift t) (box_binder lift b)
  | Ind (id, ts) -> _Ind id (box_map lift ts)
  | Constr (id, ts) -> _Constr id (box_map lift ts)
  | Match (t, mot, pbs) -> (
    match mot with
    | Mot0 -> _Match (lift t) _Mot0 (box_map (box_binder_p lift) pbs)
    | Mot1 mt ->
      _Match (lift t)
        (_Mot1 (box_binder_p lift mt))
        (box_map (box_binder_p lift) pbs)
    | Mot2 mt ->
      _Match (lift t)
        (_Mot2 (box_binder (box_binder_p lift) mt))
        (box_map (box_binder_p lift) pbs))
  | Axiom (id, t) -> _Axiom id (lift t)