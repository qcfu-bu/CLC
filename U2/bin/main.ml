open U2
open Bindlib
open Terms
open Elab
open Context
let x = mk "x"
let t = unbox (_Lambda (bind_var x (_V x)))
let ty = unbox (_Arrow _Type _Type)

let _, c = elab Ctx.empty t ty 

let _ = Format.printf "%a@." (Util.pp pp_eq) c