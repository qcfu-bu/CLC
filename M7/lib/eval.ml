open Bindlib
open Terms
open Equality

let rec eval = function
  | Empty -> failwith "missing main"
  | Define (t, tp) ->
    let x, _ = unbind tp in
    let t = nf t in
    if (name_of x = "main") then nf t
    else eval (subst tp t)
  | Datype (_, tp) -> eval tp
