open Bindlib

type term =
  | Var of term var
  | Type
  | Prod   of int * term * (term, term) binder
  | Lambda of int * term * (term, term) binder
  | Fix    of int * term * (term, term) binder
  | App    of term * term
  | Magic

type tvar = term var

let _Var = box_var

let _Type = box Type

let _Prod = box_apply3 (fun q t b -> Prod (q, t, b))

let _Lambda = box_apply3 (fun q t b -> Lambda (q, t, b))

let _Fix = box_apply3 (fun q t b -> Fix (q, t, b))

let _App = box_apply2 (fun t1 t2 -> App (t1, t2))

let _Magic = box Magic

let rec lift = function
  | Var x -> _Var x
  | Type  -> _Type
  | Prod (q, t, b) -> 
    _Prod (box q) (lift t) (box_binder lift b)
  | Lambda (q, t, b) ->
    _Lambda (box q) (lift t) (box_binder lift b)
  | Fix (q, t, b) ->
    _Fix (box q) (lift t) (box_binder lift b)
  | App (t1, t2) ->
    _App (lift t1) (lift t2)
  | Magic -> _Magic