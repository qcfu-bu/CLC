open Fmt
open Lang
open Names
open Syntax1

let x = V.mk "x"
let y = V.mk "y"
let foo = bind_tm x (Var x)