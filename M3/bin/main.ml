open Bindlib
open M3
open Rig
open Terms
open Norms
open Context
open Typec

let f = mk "f"
let g = mk "g"
let x = mk "x"
let y = mk "y"
let a = mk "a"

let ty1 = 
  _Prod _Zero _Type (bind_var a (
    _Prod _One (_Prod _One (_Var a) (bind_var __ (_Var a))) (bind_var x (
      _Prod _W (_Var a) (bind_var __ (
        _Var a))))))

let t1 = 
  _Lambda (bind_var __ (
    _Lambda (bind_var f (
      _Lambda (bind_var x (
        _App (_Var f) (_Var x)))))))

let t = 
  _LetIn _One (_AnnTy t1 ty1) (bind_var f (
    _LetIn _One (_AnnTy t1 ty1) (bind_var g (
      (* no choice of terms here is well typed *)
      _Var f))))

let _ = 
  let t = unbox t in
  let p = _W in
  let ctx, ty = infer empty p t in
  let t = cbv t in
  let ty = cbv ty in
  Format.printf "complete1\n";
  Format.printf "ctx := %a\n" Context.pp ctx;
  Format.printf "t   := %a\n" Terms.pp t;
  Format.printf "q   := %a\n" Rig.pp p;
  Format.printf "ty  := %a\n" Terms.pp ty;
  Format.printf "\n"