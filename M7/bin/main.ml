open M7
open Parser
open Format
open Eval

let _ =
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let t = parse_ch ch in
    printf "%a@.@." Terms.pp_top t;
    printf "%a@.@." Terms.pp (eval t);