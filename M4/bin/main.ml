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

let one = mk "one"
let two = mk "two"
let add = mk "add"

let t1 = 
  _Axiom (_Type L) (bind_var _A (
  _Axiom (_Type L) (bind_var _B (
  _G_intro (
    _Axiom (_Var _A) (bind_var a (
    _Axiom (_Var _B) (bind_var b (
    _LetIn (_Ann (_Pair (_Var a) (_Var b)) 
                 (_Tensor (_Var _A) (_Var _B))) (bind_var x (
    _Tensor_elim (_Var x) (bind_mvar [| x; y |] (
    _Ann (_Pair (_Var x) (_U)) 
                (_Tensor (_Var _A) (_True))
    )))))))))))))

let _One = _Succ _Zero

let _ConstNat = 
  _Ann (_Const _Nat) (_Arrow _Nat (_Type I))

let _Add = 
  _Ann
    (_Lambda (bind_var x (
    _Lambda (bind_var y (
    _Nat_elim
      (_ConstNat)
      (_Var y)
      (_Const (
       _Lambda (bind_var x (
         _Succ (_Var x)))))
      (_Var x))))))
    (_Arrow _Nat (_Arrow _Nat _Nat))

let t2 = 
  _LetIn _Add (bind_var add (
  _LetIn _One (bind_var one (
  _mApp (_Var add) [_Var one; _Var one]))))

let t3 = 
  _LetIn _Add (bind_var add (
  _LetIn _One (bind_var one (
  _LetIn (_mApp (_Var add) [_Var one; _Var one]) (bind_var two (
  _G_intro 
    (_Ann
      (_Pair (_F_intro (_mApp (_Var add) [_Var two; _Var two]) _U)
             (_F_intro (_Var two) _U))
      (_Tensor
        (_F (_Nat) (bind_var x (_Unit L)))
        (_F (_Nat) (bind_var x (_Unit L)))))
  ))))))

let _ = 
  let () = is_debug := true in
  let t = unbox t2 in
  let ty = infer_i empty t in
  Format.printf "complete@.";
  Format.printf "@[t  :=@;<1 2>%a@]@." pp (nf t);
  Format.printf "@[ty :=@;<1 2>%a@]@." pp (nf ty)