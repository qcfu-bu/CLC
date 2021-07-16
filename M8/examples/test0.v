Inductive Eq (A : Type) (x : A) : A -> Type :=
| refl : Eq A x x.

Definition Eq_trans
  (A : Type)
  (x y z : A)
  (e1 : Eq A x y)
  (e2 : Eq A y z) :
  Eq A x z
:=
  match e2 in Eq _ _ y return Eq A x y with
  | refl => e1
  end.

Definition Eq_sym 
  (A : Type) 
  (x y : A) 
  (e : Eq A x y) :
  Eq A y x
:=
  match e in Eq _ _ y return Eq A y x with
  | refl => refl
  end.

Definition TyInd 
  (A : Type) 
  (x y : A)
  (P : A -> Type) 
  (e : Eq A x y)
  (f : P x) :
  P y
:= 
  match e in Eq _ _ y return P y with
  | refl => f
  end.

Definition LnInd 
  (A : Type) 
  (x y : A)
  (P : A -> Linear) 
  (e : Eq A x y)
  (f : P x) :
  P y
:= 
  match e in Eq _ _ y return P y with
  | refl => f
  end.

Inductive Unit : Type :=
| tt : Unit.

Inductive Base : Linear :=
| ll : Base.

Inductive Nat : Type :=
| O : Nat
| S : Nat -> Nat.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (add m n)
  end.

Inductive Bool : Type :=
| true : Bool
| false : Bool.

Inductive Sigma (A : Type) (F : A -> Type) : Type :=
| pair : (x : A) -> F x -> Sigma A F.

Inductive Tensor (A : Linear) (B : Linear) : Linear :=
| tpair : A -> B -> Tensor A B.

Inductive FTensor (A : Type) (F : A -> Linear) : Linear :=
| fpair : (x : A) -> F x -> FTensor A F.

Axiom unsafeC : (A : Linear) -> A -> Unit.
Axiom unsafeP : (A : Linear) -> A.

Definition Loc : Type := Nat.
Axiom PtsTo : Loc -> Type -> Linear.
Definition Ptr (A : Type) : Linear := FTensor Loc (fun l => PtsTo l A).
Axiom New  : (A : Type) -> A -> Ptr A.
Axiom Free : (A : Type) -> Ptr A -> Unit.
Axiom Get  : (A : Type) -> (l : Loc) -> PtsTo l A -> FTensor A (fun _ => PtsTo l A).
Axiom Set  : (A : Type) -> (B : Type) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.

Definition main : Unit := tt.
