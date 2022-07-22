open Fmt
open MParser
open Names
open Parser0
open Trans01

let src0, state0 =
  let ch = open_in "./lib/prelude.clc" in
  match parse_channel ch SMap.empty with
  | Success res -> res
  | Failed (s, _) -> failwith "prelude"

let nspc, cs, src1 = trans_dcls [] SMap.empty src0

let find_v s =
  match List.assoc s nspc with
  | V x -> x
  | _ -> failwith "find_v(%s)" s

let find_d s =
  match List.assoc s nspc with
  | D d -> d
  | _ -> failwith "find_d(%s)" s

let find_c s =
  match List.assoc s nspc with
  | C c -> c
  | _ -> failwith "find_c(%s)" s

let unit_d = find_d "unit"
let tt_c = find_c "tt"
let bool_d = find_d "bool"
let true_c = find_c "true"
let false_c = find_c "false"
let ex_d = find_d "ex"
let ex_intro_c = find_c "ex_intro"
let sig_d = find_d "sig"
let sig_intro_c = find_c "sig_intro"
let tnsr_d = find_d "tnsr"
let tnsr_intro_c = find_c "tnsr_intro"
let box_d = find_d "box"
let box_intro_c = find_c "box_intro"
let nat_d = find_d "nat"
let zero_c = find_c "zero"
let succ_c = find_c "succ"
let ascii_d = find_d "ascii"
let ascii0_c = find_c "Ascii"
let string_d = find_d "string"
let emptyString_c = find_c "EmptyString"
let string0_c = find_c "String"
let stdin_t = find_v "stdin_t"
let stdout_t = find_v "stdout_t"
let stderr_t = find_v "stderr_t"