open Format
open Names

type v = Name.t

type ty = t

and t =
  (* functional *)
  | Var of v
  | Meta of Meta.t
  | Ann of t * t
  | U
  | L
  | Arrow of v * t * t
  | Lolli of v * t * t
  | Lambda of p * t
  | App of t * t
  | LetIn of p * t * t
  (* inductive *)
  | Fix of v * t
  | Ind of Id.t * t list
  | Constr of Id.t * t list
  | Match of t * mot * (p * t) list
  | Axiom of Id.t * t

and p =
  | PVar of v
  | PInd of Id.t * p list
  | PConstr of Id.t * p list

and mot =
  | Mot0
  | Mot1 of p * t
  | Mot2 of v * p * t

type ind =
  { id : Id.t
  ; ty : pscope
  ; cs : constr list
  }

and constr =
  { id : Id.t
  ; ty : pscope
  }

and pscope =
  | Pbase of tscope
  | PBind of v * t * pscope

and tscope =
  | Tbase of t
  | TBind of v * t * tscope

type top =
  | Empty
  | Main of t
  | Define of v * t * top
  | Datype of ind * top

exception AppendMain

let rec pp_v = Name.pp

and pp_p fmt = function
  | PVar x -> fprintf fmt "%a" pp_v x
  | PInd (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps
  | PConstr (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps

and pp_ps fmt = function
  | [ p ] -> fprintf fmt "%a" pp_p p
  | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p p pp_ps ps
  | _ -> ()

and spine t =
  match t with
  | Lambda (x, b) ->
    let xs, t = spine b in
    (x :: xs, t)
  | _ -> ([], t)

and pp fmt t =
  let pp_aux fmt = List.iter (fun x -> fprintf fmt "%a " pp_p x) in
  match t with
  | Var x -> fprintf fmt "%a" pp_v x
  | Meta x -> fprintf fmt "%a" Meta.pp x
  | Ann (s, t) -> fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp s pp t
  | U -> fprintf fmt "U"
  | L -> fprintf fmt "L"
  | Arrow (x, ty, b) ->
    if Name.string_of x = "_" then
      fprintf fmt "@[%a ->@;<1 2>%a@]" pp ty pp b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]" pp_v x pp ty pp b
  | Lolli (x, ty, b) ->
    if Name.string_of x = "_" then
      fprintf fmt "@[%a -o@;<1 2>%a@]" pp ty pp b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a) -o@]@;<1 2>%a@]" pp_v x pp ty pp b
  | Lambda (x, b) ->
    let ps, b = spine b in
    fprintf fmt "@[fun %a %a=>@;<1 2>%a@]" pp_p x pp_aux ps pp b
  | Fix (x, b) ->
    let ps, b = spine b in
    fprintf fmt "@[fix %a %a=>@;<1 2>%a@]" pp_v x pp_aux ps pp b
  | App (s, t) -> fprintf fmt "@[(%a)@;<1 2>%a@]" pp s pp t
  | LetIn (p, t, b) ->
    fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" pp_p p pp t pp b
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
  | Mot1 (p, b) -> fprintf fmt " in %a return@;<1 2>%a" pp_p p pp b
  | Mot2 (x, p, b) ->
    fprintf fmt " as %a in %a return@;<1 2>%a" pp_v x pp_p p pp b

and pp_cl fmt (p, t) = fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp t

and pp_cls fmt = function
  | cl :: cls -> fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls
  | _ -> ()

let rec pp_top fmt = function
  | Empty -> ()
  | Main t -> fprintf fmt "@[Definition main :=@;<1 2>%a.@]" pp t
  | Define (x, t, tp) -> (
    match t with
    | Axiom (_, ty) ->
      fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" pp_v x pp ty pp_top tp
    | _ ->
      fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" pp_v x pp t pp_top tp)
  | Datype (ind, tp) ->
    fprintf fmt "@[Inductive %a %a :=@.%a@.@.%a@]" Id.pp ind.id pp_pscope ind.ty
      pp_constr ind.cs pp_top tp

and pp_pscope fmt = function
  | Pbase t -> fprintf fmt ": %a" pp_tscope t
  | PBind (x, ty, b) ->
    if Name.string_of x = "_" then
      fprintf fmt "@[%a@;<1 2>%a@]" pp ty pp_pscope b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a)@]@;<1 2>%a@]" pp_v x pp ty pp_pscope b

and pp_tscope fmt = function
  | Tbase t -> fprintf fmt "%a" pp t
  | TBind (x, ty, b) ->
    if Name.string_of x = "_" then
      fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp ty pp_tscope b
    else
      fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]" pp_v x pp ty pp_tscope b

and pp_constr fmt = function
  | [ c ] -> fprintf fmt "@[| %a %a.@]" Id.pp c.id pp_pscope c.ty
  | c :: cs ->
    fprintf fmt "@[<v 0>| %a %a@;<1 0>%a@]" Id.pp c.id pp_pscope c.ty pp_constr
      cs
  | _ -> ()

let rec append_top top1 top2 =
  match top1 with
  | Empty -> top2
  | Main _ -> raise AppendMain
  | Define (v, t, top1) -> Define (v, t, append_top top1 top2)
  | Datype (tcons, top1) -> Datype (tcons, append_top top1 top2)
