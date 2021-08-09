open Bindlib
open U0
open Terms
open Unify

let a = Const "A"

let x = mk "x"
let f = mk "f"

let vctx = [
  (x, a);
  (f, Fun (a, a));
]

let mx = M.mk "X" (Fun (a, a))

let ps = [
  (_App (_M mx) (_App (_V f) (_V x)), _App (_V f) (_V x));
  (_App (_M mx) (_App (_V f) (_V x)), _App (_V f) (_App (_M mx) (_V x)));
]
let ps = List.map (fun (t1, t2) -> (unbox t1, unbox t2)) ps

let _ = unify vctx ps