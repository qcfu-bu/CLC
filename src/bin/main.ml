open Cclc
open Core
open Name

let id = Id.mk "pair"

let m =
  Constr (id, [Knd U; Knd L])

let x = Var.mk "x"

let y = Var.mk "y"

let p = PConstr (id, [x; y])

let n =
  let y = Var.map ((+) 1) y in
  Match (m, Mot0, [(p, App (Var x, Var y))])

let w = whnf n
