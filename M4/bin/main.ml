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

let pf = mk "pf"

let _One = (_Succ _Zero)

let _ConstNat = 
  (_Ann (_Const _Nat) (_Arrow _Nat (_Type I)))

let _Add = 
  (_Ann
    (_Lambda (bind_var x 
    (_Lambda (bind_var y 
    (_Nat_elim
      (_ConstNat)
      (_Var y)
      (_Const 
      (_Lambda (bind_var x 
        (_Succ (_Var x)))))
      (_Var x))))))
    (_Arrow _Nat (_Arrow _Nat _Nat)))

let _Lemma0 =
  (* t := fun x y _ => S x === S y
   * t :: forall x y : Nat, x === y -> U *)
  (_Ann
    (_Lambda (bind_var x 
      (_Lambda (bind_var y 
        (_Const (_Eq (_Succ (_Var x)) 
                     (_Succ (_Var y)) 
                     (_Nat)))))))
    (_Prod _Nat (bind_var x 
      (_Prod _Nat (bind_var y 
        (_Arrow 
          (_Eq (_Var x) (_Var y) _Nat)
          (_Type I)))))))

let _Lemma1 =
  (* forall x : Nat, lemma(x, x, refl x) *)
  (_Ann
    (_Lambda (bind_var x 
      (_Refl (_Succ (_Var x)))))
    (_Prod _Nat (bind_var x 
      (_mApp _Lemma0 [_Var x; _Var x; _Refl (_Var x)]))))

let _Lemma =
  (_Ann
    (_Lambda (bind_var x
      (_Lambda (bind_var y
        (_Lambda (bind_var pf 
          (_Ind _Lemma0 _Lemma1 (_Var x) (_Var y) (_Var pf))))))))
    (_Prod _Nat (bind_var x 
      (_Prod _Nat (bind_var y 
        (_Arrow 
          (_Eq (_Var x) (_Var y) _Nat)
          (_Eq (_Succ (_Var x)) (_Succ (_Var y)) _Nat)))))))

let _Theorem0 =
  (* Nat -> Type *)
  (_Ann 
    (_Lambda (bind_var x 
      (_Eq (_mApp _Add [_Var x; _Zero]) (_Var x) _Nat)))
    (_Arrow _Nat (_Type I)))

let _Theorem1 =
  (_Ann 
    (_Refl _Zero)
    (_App _Theorem0 _Zero))

let _Theorem2 =
  (_Ann
    (_Lambda (bind_var x 
      (_Lambda (bind_var pf
        (_mApp _Lemma 
          [ _mApp _Add [_Var x; _Zero]
          ; _Var x
          ; _Var pf])))))
    (_Prod _Nat (bind_var x 
      (_Arrow (_App _Theorem0 (_Var x)) 
              (_App _Theorem0 (_Succ (_Var x)))))))

let _Theorem =
  (_Ann
    (_Lambda (bind_var x
      (_Nat_elim _Theorem0 _Theorem1 _Theorem2 (_Var x))))
    (_Prod _Nat (bind_var x 
      (_Eq (_mApp _Add [_Var x; _Zero]) (_Var x) _Nat))))

let _ = 
  let () = is_debug := true in
  let t = unbox _Theorem
  in
  let ty = infer_i empty t in
  Format.printf "complete@.";
  Format.printf "@[t  :=@;<1 2>%a@]@." pp (nf t);
  Format.printf "@[ty :=@;<1 2>%a@]@." pp (nf ty)