Inductive Eq (A : U) (x : A) : A -> U :=
| refl : Eq A x x.

Definition Eq_trans
  (A : U)
  (x y z : A)
  (e1 : Eq A x y)
  (e2 : Eq A y z) :
  Eq A x z
:=
  match e2 in Eq _ _ y return Eq A x y with
  | refl => e1
  end.

Definition Eq_sym 
  (A : U) 
  (x y : A) 
  (e : Eq A x y) :
  Eq A y x
:=
  match e in Eq _ _ y return Eq A y x with
  | refl => refl
  end.

Definition TyInd 
  (A : U) 
  (x y : A)
  (P : A -> U) 
  (e : Eq A x y)
  (f : P x) :
  P y
:= 
  match e in Eq _ _ y return P y with
  | refl => f
  end.

Definition LnInd 
  (A : U) 
  (x y : A)
  (P : A -> L) 
  (e : Eq A x y)
  (f : P x) :
  P y
:= 
  match e in Eq _ _ y return P y with
  | refl => f
  end.

Inductive Unit : U :=
| tt : Unit.

Inductive Base : L :=
| ll : Base.

Inductive Nat : U :=
| O : Nat
| S : Nat -> Nat.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (add m n)
  end.

Inductive Bool : U :=
| true : Bool
| false : Bool.

Inductive Sigma (A : U) (F : A -> U) : U :=
| pair : (x : A) -> F x -> Sigma A F.

Inductive Tensor (A : L) (B : L) : L :=
| tpair : A -> B -> Tensor A B.

Inductive FTensor (A : U) (F : A -> L) : L :=
| fpair : (x : A) -> F x -> FTensor A F.

Axiom unsafeC : (A : L) -> A -> Unit.
Axiom unsafeP : (A : L) -> A.

Definition Loc : U := Nat.
Axiom PtsTo : Loc -> U -> L.
Definition Ptr (A : U) : L := FTensor Loc (fun l => PtsTo l A).
Axiom New  : (A : U) -> A -> Ptr A.
Axiom Free : (A : U) -> Ptr A -> Unit.
Axiom Get  : (A : U) -> (l : Loc) -> PtsTo l A -> FTensor A (fun _ => PtsTo l A).
Axiom Set  : (A : U) -> (B : U) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.
