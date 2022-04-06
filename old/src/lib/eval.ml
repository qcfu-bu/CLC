open Bindlib
open Util
open Terms
open Equality

let rec eval = function
  | Main t -> nf t
  | Define (t, tp) ->
    let t = nf t in
    eval (subst tp t)
  | Datype (_, tp) -> eval tp