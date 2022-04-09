open Bindlib
open Cclc
open Core
open Name
open Term
open Eval

let main = mk "main"

let x = mk "x"

let _m =
  _Fork (_Knd U) (_Var main) (bind_var x (_App (_Send (_Var x)) (_Knd L)))

let m = unbox _m

let env = VMap.singleton main EvalTerm.VBox

let v = EvalTerm.eval env m