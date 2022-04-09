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

let _ = EvalTerm.eval env m

open Top

let stdout_v = mk "stdout_v"

let _t =
  _Import Id.stdout_id (_Knd L)
    (bind_var stdout_v
       (_Define
          (_App
             (_Send (_Var stdout_v))
             (Term._Constr Id.pair_id (box_list [ _Knd U; _Knd L ])))
          (bind_var Term.blank (_Main (_Var main)))))

let t = unbox _t

let _ = EvalTop.eval env t
