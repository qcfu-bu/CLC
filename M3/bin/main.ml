open Bindlib
open M3
open Rig
open Terms
open Norms
open Context
open Typec

let tensor = mk "tensor"
let tensorTy =
  _Arrow _Zero _Type (_Arrow _Zero _Type _Type)

let nat = mk "Nat"
let natTy = _Type

let str = mk "String"
let strTy = _Type

let vec = mk "Vec"
let vecTy =
  _Arrow _Zero (_Var nat) _Type

let channel = mk "Channel"
let channelTy = _Type

let rep = mk "rep"
let repTy = 
  let x = mk "x" in
  _Prod _W (_Var nat) (bind_var x (
    _App (_Var vec) (_Var x)))

let ch = mk "ch"
let chTy = _Var channel

let nat_channel = 
  _App (_App (_Var tensor) (_Var nat)) (_Var channel)

let getnum = mk "getnum"
let getnumTy =
  _Arrow _One (_Var channel) nat_channel

let fst = mk "fst"
let fstTy =
  _Arrow _One nat_channel (_Var nat)

let snd = mk "snd"
let sndTy =
  _Arrow _One nat_channel (_Var channel)

let t1 =
  let x = mk "x" in
  _Axiom _Zero tensorTy (bind_var tensor (
  _Axiom _Zero natTy (bind_var nat (
  _Axiom _Zero strTy (bind_var str (
  _Axiom _Zero vecTy (bind_var vec (
  _Axiom _Zero channelTy (bind_var channel (
  _Axiom _W repTy (bind_var rep (
  _Axiom _One chTy (bind_var ch (
  _Axiom _W getnumTy (bind_var getnum (
  _Axiom _W fstTy (bind_var fst (
  (* very subtle *)
  _LetIn _One (_App (_Var fst) (_App (_Var getnum) (_Var ch))) 
    (* (bind_var x (_App (_Var rep) (_Var x))) *)
    (bind_var x (_Var x))
  ))))))))))))))))))

let t2 = 
  let _A = mk "A" in
  let _B = mk "B" in
  let f = mk "f" in
  let x = mk "x" in
  _Axiom _Zero _Type (bind_var _A (
  _Axiom _Zero _Type (bind_var _B (
  _Axiom _W (_Arrow _One (_Var _A) (_Var _B)) (bind_var f (
  _Axiom _W (_Var _A) (bind_var x (
  _App (_Var f) (_Var x)
  ))))))))

let _ = 
  let t = unbox t1 in
  let p = _One in
  let ctx, ty = infer empty p t in
  let t = t in
  let ty = cbv ty in
  Format.printf "complete1\n";
  Format.printf "ctx := %a\n" Context.pp ctx;
  Format.printf "t   := %a\n" Terms.pp t;
  Format.printf "q   := %a\n" Rig.pp p;
  Format.printf "ty  := %a\n" Terms.pp ty;
  Format.printf "\n"