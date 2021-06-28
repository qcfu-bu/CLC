open M8
open Rparser
open Format
open Desugar
open Tcheck
open Eval

let _ =
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let top = parse_ch ch in
    printf "%a@.@." Raw.pp_top top;
    let top = desugar top in
    printf "%a@.@." Terms.pp_top top;
    let _ = tcheck top in
    printf "%a@.@." Terms.pp (eval top);