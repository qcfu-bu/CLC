open Cclc
open Core
open Name
open Term

let id = Id.mk "pair"

let a = Var.mk "a"

let b = Var.incr 1 (Var.mk "b")

let c = Var.incr 2 (Var.mk "c")

let m = Constr (id, [ Var a; Var b; Var c ])

let x = Var.mk "x"

let y = Var.mk "y"

let z = Var.mk "z"

let p = PConstr (id, [ x; y; z ])

let n =
  let y = Var.incr 1 y in
  let z = Var.incr 2 z in
  Match (m, Mot0, [ (p, App (Var z, App (Var x, Var y))) ])

let w = whnf n