open Fmt
open Lang
open Names
open Parser0

let parse s =
  let ch = open_in s in
  try
    match parse_channel ch with
    | Success dcl ->
      let _ = pr "%a\n" Syntax0.pp_decls dcl in
      let _ = pr "----------------------------------------------@." in
      let _, _, dcl = Trans01.trans_decls SMap.empty SMap.empty dcl in
      let _ = pr "%a\n" Syntax1.pp_decls dcl in
      ()
    | Failed (s, _) -> epr "%s\n" s
  with
  | Failure s -> epr "Failure: %s" s

let _ = parse "mock/mock0.clc"