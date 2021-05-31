open Bindlib
open M3
open Rig
open Terms
open Context
open Typec

let f = new_var (fun x -> Var x) "f"
let g = new_var (fun x -> Var x) "g"
let x = new_var (fun x -> Var x) "x"
let y = new_var (fun x -> Var x) "y"

let a = new_var (fun x -> Var x) "a"

let ty1 = 
  _Prod _Zero _Type (bind_var a (
    _Prod _One (_Var a) (bind_var x (
      _Prod _W (_Var a) (bind_var y (
        _Var a))))))
let t1 = 
  _Lambda (bind_var a (
    _Lambda (bind_var x (
      _Lambda (bind_var y (
        _Var x))))))

let t = _Ann t1 ty1

let _ = 
  let t = unbox t in
  infer empty _W t