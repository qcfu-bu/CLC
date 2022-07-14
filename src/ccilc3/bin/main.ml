open Fmt
open Lang
open Syntax0
open Parser0

let parse s =
  let ch = open_in s in
  match parse_channel ch with
  | Success dcl -> pr "%a\n" (list ~sep:cut pp_decl) dcl
  | Failed (s, _) -> pr "%s\n" s

let _ = parse "mock/mock0.txt"