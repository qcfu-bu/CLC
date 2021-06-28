open Format
open Names

type v = Name.t

type t =
  (* functional *)
  | Var of v
  | Ann of t * t
  | Type
  | Linear
  | TyProd of v * t * t
  | LnProd of v * t * t
  | Lambda of p * t
  | Fix    of v * t
  | App    of t * t
  | LetIn  of p * t * t
  (* data *)
  | TCons  of Id.t * t list
  | DCons  of Id.t * t list
  | Match  of t * motive option 
                * (p * t)  list
  | Axiom  of Id.t * t
and p = 
  | PVar    of v
  | PDCons  of Id.t * p list
  | PTCons  of Id.t * p list
and motive = v * p * t

type tcons = 
  TConstr of Id.t * pscope * dcons list
and dcons = 
  DConstr of Id.t * pscope 
and pscope =
  | PBase of tscope
  | PBind of v * t * pscope
and tscope = 
  | TBase of t
  | TBind of v * t * tscope

type top =
  | Empty
  | Define of v * t * top
  | Datype of tcons * top

let rec pp_v = Name.pp

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
  | Lambda (x, b) ->
    let xs, t = spine b in
    (x :: xs, t)
  | _ -> ([], t)

and pp fmt t = 
  let pp_aux fmt =
    List.iter (fun x -> 
      fprintf fmt "%a " pp_p x)
  in
  match t with
  | Var x -> 
    fprintf fmt "%a" pp_v x
  | Ann (s, t) -> 
    fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp s pp t
  | Type -> fprintf fmt "Type"
  | Linear -> fprintf fmt "Linear"
  | TyProd (x, ty, b) -> 
    if (Name.string_of x = "_") 
    then fprintf fmt "@[%a ->@;<1 2>%a@]" pp ty pp b
    else fprintf fmt "@[@[(%a :@;<1 2>%a) ->@]@;<1 2>%a@]"
      pp_v x pp ty pp b
  | LnProd (x, ty, b) -> 
    if (Name.string_of x = "_") 
    then fprintf fmt "@[%a >>@;<1 2>%a@]" pp ty pp b
    else fprintf fmt "@[@[(%a :@;<1 2>%a) >>@]@;<1 2>%a@]"
      pp_v x pp ty pp b
  | Lambda (x, b) ->
    let ps, b = spine b in
    fprintf fmt "@[fun %a %a=>@;<1 2>%a@]"
      pp_p x pp_aux ps pp b
  | Fix (x, b) ->
    let ps, b = spine b in
    fprintf fmt "@[fix %a %a=>@;<1 2>%a@]"
      pp_v x pp_aux ps pp b
  | App (s, t) ->
    fprintf fmt "@[(%a)@;<1 2>%a@]" pp s pp t
  | LetIn (p, t, b) -> 
    fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      pp_p p pp t pp b
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
  | Some (x, p, b) ->
    if (Name.string_of x = "_")
    then fprintf fmt " in %a return@;<1 2>%a" pp_p p pp b
    else fprintf fmt " as %a in %a return@;<1 2>%a" pp_v x pp_p p pp b
  | None -> ()

and pp_cl fmt (p, t) =
  fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp t

and pp_cls fmt = function
  | cl :: cls ->
    fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls
  | _ -> ()

let rec pp_top fmt = function
  | Empty -> ()
  | Define (x, t, tp) -> (
    match t with
    | Axiom (_, ty) ->
      fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" 
        pp_v x pp ty pp_top tp
    | _ ->
      fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" 
        pp_v x pp t pp_top tp)
  | Datype (dcs, tp) ->
    let TConstr (id, ts, cs) = dcs in
    fprintf fmt "@[Inductive %a %a :=@.%a@.@.%a@]" 
      Id.pp id pp_pscope ts pp_dcons cs pp_top tp

and pp_pscope fmt = function
  | PBase t -> fprintf fmt ": %a" pp_tscope t
  | PBind (x, ty, b) ->
    if (Name.string_of x = "_") 
    then fprintf fmt "@[%a@;<1 2>%a@]" pp ty pp_pscope b
    else fprintf fmt "@[@[(%a :@;<1 2>%a)@]@;<1 2>%a@]"
      pp_v x pp ty pp_pscope b
    
and pp_tscope fmt = function
  | TBase t -> fprintf fmt "%a" pp t
  | TBind (x, ty, b) ->
    if (Name.string_of x = "_") 
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

let rec append_top top1 top2 =
  match top1 with
  | Empty -> top2
  | Define (v, t, top1) ->
    Define (v, t, append_top top1 top2)
  | Datype (tcons, top1) ->
    Datype (tcons, append_top top1 top2)