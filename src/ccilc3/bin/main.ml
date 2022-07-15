open Fmt
open Lang
open Names
open Parser0
open Equality1

let parse s =
  let ch = open_in s in
  try
    match parse_channel ch with
    | Success dcls ->
      let _ = pr "%a@." Syntax0.pp_decls dcls in
      let _ = pr "----------------------------------------------@." in
      let _, _, dcls = Trans01.trans_decls SMap.empty SMap.empty dcls in
      let _ = pr "%a@." Syntax1.pp_decls dcls in
      let _ = pr "----------------------------------------------@." in
      let _ = pr "%a@." Pprint1.pp_decls dcls in
      let _ = pr "----------------------------------------------@." in
      let dcls = eval rd_all VMap.empty dcls in
      let _ = pr "%a@." Pprint1.pp_decls dcls in
      ()
    | Failed (s, _) -> epr "%s\n" s
  with
  | Failure s -> epr "Failure: %s" s

let _ = parse "mock/mock0.clc"