open Fmt
open Names
open Syntax1

let rec pp_p fmt p =
  match p with
  | PVar x -> V.pp fmt x
  | PCons (c, []) -> C.pp fmt c
  | PCons (c, ps) -> pf fmt "%a %a" C.pp c (pp_ps sp) ps
  | PAbsurd -> pf fmt "absurd"

and pp_ps sep fmt ps = pf fmt "%a" (list ~sep pp_p) ps

(* let rec pp_tm fmt m = *)