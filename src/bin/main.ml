open Format
open Bindlib
open Cclc
open Core
open Raw
open Name
open Parser
open Eval

let _ =
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let rtp = ParseTop.parse_ch ch in
    let tp = RTop.core rtp in
    let _ = printf "%a@.@." Top.pp tp in
    let _ = EvalTop.eval tp in
    ()
