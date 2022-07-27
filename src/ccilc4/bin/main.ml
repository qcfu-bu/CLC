open Fmt
open Lang
open Names
open Parser0
open Prelude
open Equality1

let parse s =
  let ch = open_in s in
  try
    match parse_channel ch state0 with
    | Success (dcls, _) ->
      let _ = pr "%a@." Syntax0.pp_dcls dcls in
      let _ = pr "----------------------------------------------@." in
      let _, _, dcls = Trans01.trans_dcls nspc cs dcls in
      let dcls = src1 @ dcls in
      let _ = pr "%a@." Syntax1.pp_dcls dcls in
      let _ = pr "----------------------------------------------@." in
      let _ = pr "%a@." Pprint1.pp_dcls dcls in
      let _ = pr "----------------------------------------------@." in
      let res = eval rd_all VMap.empty dcls in
      let _ = pr "%a@." Pprint1.pp_dcls res in
      ()
    | Failed (s, _) -> epr "%s\n" s
  with
  | Failure s -> epr "Failure: %s" s

let _ = parse "mock/mock0.clc"
