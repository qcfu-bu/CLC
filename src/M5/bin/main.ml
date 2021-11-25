open M5
open Bindlib
open Rig
open Constr
open Context
open Tcheck

let runtime = mk "runtime"
let io = mk "io"
let stdio = mk "stdio"
let openCh = mk "openCh"
let closeCh = mk "closeCh"
let channel = mk "channel"
let ch = mk "ch"
let ch1 = mk "ch1"
let ch2 = mk "ch2"
let readn = mk "readn"

let u = mk "unit"
let nat = mk "nat"
let addn = mk "addn"
let one = mk "one"
let zero = mk "zero"

let x = mk "x"
let y = mk "y"
let z = mk "z"
let a = mk "a"
let b = mk "b"
let c = mk "c"
let m = mk "m"
let n = mk "n"
let f = mk "f"
let g = mk "g"

let add v ty q ctx =
  add v (unbox ty, Zero, q) ctx

let t =
  axiom u ty @@
  axiom nat ty @@
  axiom zero !nat @@
  axiom one !nat @@
  axiom addn (!nat --> (!nat --> !nat)) @@
  axiom channel ln @@
  axiom openCh (!nat --> !channel) @@
  axiom closeCh (!channel --> !u) @@
  axiom readn (!channel --> (!nat * !channel)) @@
  let_ ch (!openCh $ !one) @@
  let_pair (n, ch) (!readn $ !ch) @@
  (* let_ __ (!closeCh $ !ch) @@ *)
  (!addn $ !n $ !n)

let _ = 
  let _ = Tcheck.is_debug := true in
  let t = unbox t in
  let pre_ctx = empty in
  let ty, post_ctx = infer pre_ctx t in
  let () = assert_msg (Context.same pre_ctx post_ctx) "main" in
  Format.printf "complete\n";
  Format.printf "ty :=%a\n" Terms.pp ty