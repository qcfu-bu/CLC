open Format
open Bindlib
open Cclc
open Core
open Raw
open Name
open Parser
open Elab
open Tcheck
open Pprint
open Eval

let _ =
  if Array.length Sys.argv < 1 then
    printf "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let log = open_out "log.clc" in
    let rtp = ParseTop.parse_ch ch in
    let tp = RTop.core rtp in
    let s = asprintf "%a@.@." PrintTop.pp tp in
    let _ = Printf.fprintf log "desugar ok\n" in
    let _ =
      Printf.fprintf log "----------------------------------------";
      Printf.fprintf log "----------------------------------------\n"
    in
    let _ = Printf.fprintf log "%s" s in
    let tp = elab tp in
    let s = asprintf "%a@.@." PrintTop.pp tp in
    let _ = Printf.fprintf log "elab ok\n" in
    let _ =
      Printf.fprintf log "----------------------------------------";
      Printf.fprintf log "----------------------------------------\n"
    in
    let _ = Printf.fprintf log "%s" s in
    let _ = infer tp in
    let _ =
      Printf.fprintf log "----------------------------------------";
      Printf.fprintf log "----------------------------------------\n"
    in
    let _ = Printf.fprintf log "tcheck ok" in
    let _ = EvalTop.eval tp in
    ()
