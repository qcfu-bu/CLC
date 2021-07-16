Inductive LnEq (A : Linear) (x~ : A) : (_~ : A) -> Type :=
| ln_refl : LnEq A x x.

Definition LnEq_trans
  (A : Linear)
  (x~ y~ z~ : A)
  (e1 : LnEq A x y)
  (e2 : LnEq A y z) :
  LnEq A x z
:= 
  match e2 in LnEq _ _ y return LnEq A x y with
  | ln_refl => e1
  end.

Definition LnEq_sym 
  (A : Linear)
  (x~ y~ : A)
  (e : LnEq A x y) :
  LnEq A y x
:= 
  match e in LnEq _ _ y return LnEq A y x with
  | ln_refl => ln_refl
  end.

Inductive LnSigma (A : Linear) (F : (_ : A) -> Type) : Type :=
| ln_pair : (x~ : A) -> F x -> LnSigma A F.

(* Definition main : Unit := tt. *)
