open M7
open Parser
open Format
open Context
open Tcheck
open Eval

let _ =
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let top = parse_ch ch in
    printf "%a@.@." Terms.pp_top top;
    let v_ctx, _ = infer_top VarMap.empty IdMap.empty top in
    printf "v_ctx  := %a@.@." Context.pp v_ctx;
    printf "%a@.@." Terms.pp (eval top);