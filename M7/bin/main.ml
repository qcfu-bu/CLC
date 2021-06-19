open M7
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
    let v_ctx, _ = infer top in
    printf "v_ctx  := %a@.@." Context.pp v_ctx;
    printf "%a@.@." Terms.pp (eval top);