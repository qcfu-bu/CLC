open Bindlib
open M3
open Rig
open Terms
open Norms
open Context
open Typec

let f = new_var (fun x -> Var x) "f"
let g = new_var (fun x -> Var x) "g"
let x = new_var (fun x -> Var x) "x"
let y = new_var (fun x -> Var x) "y"

let a = new_var (fun x -> Var x) "a"
let __ = new_var (fun x -> Var x) ""

let ty1 = 
  _Prod _Zero _Type (bind_var a (
    _Prod _One (_Prod _One (_Var a) (bind_var __ (_Var a))) (bind_var x (
      _Prod _W (_Var a) (bind_var __ (
        _Var a))))))

(* let t1 = 
  _Lambda (bind_var __ (
    _Lambda (bind_var f (
      _Lambda (bind_var a (
        _App (_Var f) (_Var a))))))) *)

let t1 = 
  _Lambda (bind_var __ (
    _Lambda (bind_var f (
      _Lambda (bind_var a (
        _Var a))))))

let t = _Ann t1 ty1

let _ = 
  let t = unbox t in
  let p = _W in
  let ctx, ty = infer empty p t in
  let t = cbv t in
  let ty = cbv ty in
  Format.printf "complete\n";
  Format.printf "ctx := %a\n" Context.pp ctx;
  Format.printf "t   := %a\n" Terms.pp t;
  Format.printf "q   := %a\n" Rig.pp p;
  Format.printf "ty  := %a\n" Terms.pp ty;
  Format.printf "\n";