open M5
open Bindlib
open Constr
open Context
open Tcheck


let nat = mk "nat"
let add = mk "add"

let one = mk "one"
let channel = mk "channel"
let ch1 = mk "ch1"
let ch2 = mk "ch2"
let read = mk "read"
let x = mk "x"
let y = mk "y"
let f = mk "f"
let bad = mk "bad"

let t =
  axiom nat ty @@
  axiom channel ln @@
  axiom ch1 (!channel) @@
  axiom ch2 (!channel) @@
  axiom read (!channel --> (!nat ->> !channel)) @@
  axiom one (!nat) @@
  axiom add (!nat --> (!nat --> !nat)) @@
  let_ x (!read $ !ch1) @@
  let_ y (!read $ !ch2) @@
  (!x)

let _ = 
  let _ = Tcheck.is_debug := true in
  let t = unbox t in
  let ty, _ = infer empty t in
  Format.printf "complete\n";
  Format.printf "ty :=%a\n" Terms.pp ty