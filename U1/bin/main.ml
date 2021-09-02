open U1
open Bindlib
open Surface
open Elab

let x = mk "x"
let t = unbox (_Lambda (bind_var x (_V x)))
let ty = unbox (_Arrow _Type _Type)

let mctx, _, c = elab [] [] t ty 

let _ = Format.printf "%a@." pp_m mctx
let _ = Format.printf "%a@." pp_u c