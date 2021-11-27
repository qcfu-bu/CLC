open Cilc
open Bindlib
open Rparser
open Format
open Desugar
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
    let _ = infer top in
    let _ = printf "tcheck ok@." in
    let _ = printf "----------------------------------------" in
    let _ = printf "----------------------------------------@." in
    printf "%a@." Terms.pp_top top;
    let _ = printf "----------------------------------------" in
    let _ = printf "----------------------------------------@." in
    printf "%a@." Terms.pp (eval top);
