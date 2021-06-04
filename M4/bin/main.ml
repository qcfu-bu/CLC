open Bindlib
open M4
open Terms
open Norms
open Context
open Tcheck

let _A = mk "A"
let _B = mk "B"

let a = mk "a"
let b = mk "b"

let x = mk "x"
let y = mk "y"

let t1 = 
  _Axiom (_Type L) (bind_var _A (
  _Axiom (_Type L) (bind_var _B (
  _G_intro (
    _Axiom (_Var _A) (bind_var a (
    _Axiom (_Var _B) (bind_var b (
    _LetIn (_Ann (_Pair (_Var a) (_Var b)) 
                 (_Tensor (_Var _A) (_Var _B))) (bind_var x (
      (_Ann _U _True)
    )))))))))))

let _ = 
  let t = unbox t1 in
  let ty = infer_i empty t in
  Format.printf "t  := %a\n" pp (nf t);
  Format.printf "ty := %a\n" pp (nf ty)