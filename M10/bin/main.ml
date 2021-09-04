open M10
open Bindlib
open Rparser
open Format
open Desugar
open Context
open Elab
open Unify
open Tcheck
open Eval

let _ =
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let top = parse_ch ch in
    let _ = printf "parse ok@." in
    let top = desugar top in
    let _ = printf "desugar ok@." in
    let mmap = elab top in
    let _ = printf "elab ok@." in
    let top = unbox (resolve_top mmap top) in
    let _ = printf "resolve ok@." in
    let ctx, _, _ = infer MetaMap.empty top in
    let _ = printf "tcheck ok@." in
    printf "%a@.@." Terms.pp_top top;
    assert_msg (VarMap.is_empty ctx) "non-clean context";
    printf "%a@.@." Terms.pp (eval top);
