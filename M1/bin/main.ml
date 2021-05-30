open M1
open Names
open Constr
open Context
open Typecheck

let ty =
  let x = Id.of_string "x" in
  let br = { binder = Name.Name x; annot = Type; q = 0 } in
  let b, t = bind br Type in
  Prod (b, t)

let t =
  let x = Id.of_string "x" in
  let br = { binder = Name.Name x; annot = Type; q = 1 } in
  let b, t = bind br (Var x) in
  Lambda (b, t)

let _ =
  let ctx = check empty Type 0 ty in
  if is_zero ctx then () else failwith "ctx"

let _ =
  let ctx = check empty Type 0 (App (t, Type)) in
  if is_zero ctx then () else failwith "ctx"
