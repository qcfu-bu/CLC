open Bindlib
open M2
open Ring
open Terms
open Context
open Typec

let f = new_var (fun x -> Var x) "f"
let g = new_var (fun x -> Var x) "g"
let x = new_var (fun x -> Var x) "x"
let y = new_var (fun x -> Var x) "y"

let a = new_var (fun x -> Var x) "a"

let _ = Typec.d := true

let ty1 = 
  _Prod z _Type (bind_var a (
    _Prod o (_Var a) (bind_var x (
      _Prod w (_Var a) (bind_var y (
        _Var a))))))
let t1 = 
  _Lambda z _Type (bind_var a (
    _Lambda o (_Var a) (bind_var x (
      _Lambda w (_Var a) (bind_var y (
        _Var x))))))

let _ = 
  let ty1 = unbox ty1 in
  let t1 = unbox t1 in
  let ctx = check empty ty1 o t1 in
  assert (is_zero ctx)