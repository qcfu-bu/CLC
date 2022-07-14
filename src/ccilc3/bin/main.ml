open Fmt
open Lang
open Syntax0
open Parser0

let parse s =
  let ch = open_in s in
  match parse_channel ch with
  | Success t -> pr "%a\n" pp_tm t
  | Failed (s, _) -> pr "%s\n" s

let _ = parse "mock/mock0.txt"