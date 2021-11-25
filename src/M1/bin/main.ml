open M1
open Names
open Constr
open Context
open Typecheck

let mkProd x annot q t =
  let br = { binder = Name x; annot; q } in
  let b, t = bind br t in
  Prod (b, t)

let mkLambda x annot q t =
  let br = { binder = Name x; annot; q } in
  let b, t = bind br t in
  Lambda (b, t)

let mkFix x annot q t =
  let br = { binder = Name x; annot; q } in
  let b, t = bind br t in
  Fix (b, t)

let ty =
  let x = Id.of_string "x" in
  mkProd x Type 1 Type

let t0 =
  let x = Id.of_string "x" in
  mkLambda x Type 1 (Var x)

let t1 =
  let f = Id.of_string "f" in
  let x = Id.of_string "x" in
  let f_br = { binder = Name f; annot = ty; q = 1 } in
  let x_br = { binder = Name x; annot = Type; q = 1 } in
  let x_b, t = bind x_br (App (Var f, Var x)) in
  let f_b, t = bind f_br (Lambda (x_b, t)) in
  Fix (f_b, t)

let _ =
  let ctx = check empty ty 0 t1 in
  if is_zero ctx then () else failwith "ctx"
