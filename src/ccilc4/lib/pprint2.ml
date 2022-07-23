open Fmt
open Names
open Syntax2

let rec pp_p fmt p =
  match p with
  | PVar x -> V.pp fmt x
  | PCons (c, []) -> C.pp fmt c
  | PCons (c, ps) -> pf fmt "(%a %a)" C.pp c (pp_ps " ") ps

and pp_ps sep fmt ps =
  match ps with
  | [] -> ()
  | [ p ] -> pp_p fmt p
  | p :: ps -> pf fmt "%a%s%a" pp_p p sep (pp_ps sep) ps

let rec pp_tm fmt m =
  let rec gather_lams s m =
    match m with
    | Lam (t, abs) ->
      if s = t then
        let x, m = unbind_tm abs in
        let xs, m = gather_lams s m in
        (x :: xs, m)
      else
        ([], m)
    | _ -> ([], m)
  in
  match m with
  | Ann (a, m) -> pf fmt "@[@@[%a]@;<1 0>%a@]" pp_tm a pp_tm m
  | Meta (x, ms) -> M.pp fmt x
  | Type s -> pp_sort fmt s
  | Var x -> V.pp fmt x
  | Pi (s, a, _, abs) -> (
    let x, b = unbind_tm abs in
    match (s, occurs_tm x b) with
    | U, false -> pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tm b
    | U, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | L, false -> pf fmt "@[%a -o@;<1 2>%a@]" pp_tm a pp_tm b
    | L, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) -o@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b)
  | Fix (a, abs) ->
    let x, m = unbind_tm abs in
    let xs, m = gather_lams U m in
    pf fmt "@[fix %a%a =>@;<1 2>%a@]" V.pp x V.pps xs pp_tm m
  | Lam (s, abs) -> (
    let x, m = unbind_tm abs in
    let xs, m = gather_lams s m in
    match s with
    | U -> pf fmt "@[fun %a%a =>@;<1 2>%a@]" V.pp x V.pps xs pp_tm m
    | L -> pf fmt "@[lin %a%a =>@;<1 2>%a@]" V.pp x V.pps xs pp_tm m)
  | App _ ->
    let m, ms = unApps m in
    pf fmt "@[((%a) %a)@]" pp_tm m (list ~sep:sp pp_tm) ms
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    pf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  | Data (d, ms) -> (
    match ms with
    | [] -> D.pp fmt d
    | _ -> pf fmt "@[(%a@;<1 2>%a)@]" D.pp d (list ~sep:sp pp_tm) ms)
  | Cons (c, ms) -> (
    match ms with
    | [] -> C.pp fmt c
    | _ -> pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms)
  | Case (m, a, cls) ->
    pf fmt "@[<v 0>(@[case %a@[return@;<1 2>%a@]@;<1 0>of@]@;<1 2>%a)@]" pp_tm m
      pp_tm a pp_cls cls
  | Absurd -> pf fmt "absurd"
  | Main -> pf fmt "@main"
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (r, _, a, abs) -> (
    let x, b = unbind_tm abs in
    match (r, occurs_tm x b) with
    | true, false -> pf fmt "@[?%a ⋅@;<1 2>%a@]" pp_tm a pp_tm b
    | true, true -> pf fmt "@[?(%a : %a) ⋅@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | false, false -> pf fmt "@[!%a ⋅@;<1 2>%a@]" pp_tm a pp_tm b
    | false, true -> pf fmt "@[!(%a : %a) ⋅@;<1 2>%a@]" V.pp x pp_tm a pp_tm b)
  | Ch (r, m) ->
    if r then
      pf fmt "ch<%a>" pp_tm m
    else
      pf fmt "hc<%a>" pp_tm m
  | Fork (a, m, abs) ->
    let x, n = unbind_tm abs in
    pf fmt "@[@[fork (%a :@;<1 2>%a) <-@;<1 2>%a@;<1 0>in@]@;<1 2>%a@]" V.pp x
      pp_tm a pp_tm m pp_tm n
  | Send m -> pf fmt "send %a" pp_tm m
  | Recv (_, m) -> pf fmt "recv %a" pp_tm m
  | Close m -> pf fmt "close %a" pp_tm m

and pp_cl fmt (Cl abs) =
  let p, rhs = unbindp_tm abs in
  pf fmt "| %a =>@;<1 2>%a" pp_p p pp_tm rhs

and pp_cls fmt cls =
  match cls with
  | [] -> ()
  | [ cl ] -> pf fmt "@[%a@]" pp_cl cl
  | cl :: cls -> pf fmt "@[%a@]@;<1 2>%a" pp_cl cl pp_cls cls

let pp_trg fmt targ =
  match targ with
  | TStdin -> pf fmt "@stdin"
  | TStdout -> pf fmt "@stdout"
  | TStderr -> pf fmt "@stderr"
  | TMain -> pf fmt "@main"

let rec pp_ptl fmt ptl =
  match ptl with
  | PBase tl -> pf fmt ":@;<1 2>%a" pp_tl tl
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_ptl ptl

and pp_tl fmt tl =
  match tl with
  | TBase b -> pp_tm fmt b
  | TBind (a, _, abs) -> (
    let x, tl = unbind_tl abs in
    match occurs_tl x tl with
    | false -> pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tl tl
    | true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tl tl)

let pp_dcons fmt (DCons (c, ptl)) = pf fmt "| %a %a" C.pp c pp_ptl ptl

let rec pp_dconss fmt dconss =
  match dconss with
  | [] -> ()
  | [ dcons ] -> pf fmt "@[%a@]" pp_dcons dcons
  | dcons :: dconss -> pf fmt "@[%a@]@;<1 2>%a" pp_dcons dcons pp_dconss dconss

let pp_dcl fmt dcl =
  match dcl with
  | DTm (x, a, m) ->
    pf fmt "@[def %a :@;<1 2>%a :=@;<1 2>%a@]" V.pp x pp_tm a pp_tm m
  | DData (d, ptl, dconss) ->
    pf fmt "@[<v 0>@[data %a %a@]@;<1 2>%a@]" D.pp d pp_ptl ptl pp_dconss dconss
  | DOpen (targ, x) -> pf fmt "open %a as %a" pp_trg targ V.pp x
  | DAxiom (x, a) -> pf fmt "@[axiom %a :@;<1 2>%a@]" V.pp x pp_tm a

let rec pp_dcls fmt dcls =
  match dcls with
  | [] -> ()
  | dcl :: dcls -> pf fmt "%a@.@.%a" pp_dcl dcl pp_dcls dcls
