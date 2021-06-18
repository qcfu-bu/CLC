Inductive Unit : Type :=
| tt : Unit.

Inductive Nat : Type :=
| O : Nat
| S : Nat -> Nat.

Inductive Bool : Type :=
| true : Bool
| false : Bool.

Inductive SNat : Nat -> Type :=
| Zero : SNat O
| Succ : (n : Nat) -> SNat n -> SNat (S n).

Inductive Eq : (A : Type) -> A -> A -> Type :=
| Refl : (A : Type) -> (x : A) -> Eq A x x.

Inductive Sigma : (A : Type) -> (A -> Type) -> Type :=
| Pair : (A : Type) -> (F : A -> Type) -> (x : A) -> F x -> Sigma A F.

Inductive Tensor : Linear -> Linear -> Linear :=
| TPair : (A : Linear) -> (B : Linear) -> A -> B -> Tensor A B.

Inductive FTensor : (A : Type) -> (A -> Linear) -> Linear :=
| FPair : (A : Type) -> (F : A -> Linear) -> (x : A) -> F x -> FTensor A F.

Definition Loc : Type := Nat.

Axiom PtsTo : Loc -> Type -> Linear.
Axiom New : (A : Type) -> A -> FTensor Loc (fun l => PtsTo l A).
Axiom Free : (A : Type) -> FTensor Loc (fun l => PtsTo l A) -> Unit.
Axiom Get : (A : Type) -> (l : Loc) -> PtsTo l A -> FTensor A (fun _ => PtsTo l A).
Axiom Set : (A : Type) -> (B : Type) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.

Definition main : Unit := 
  let ft := New Nat O in
  match ft in FTensor L F return 
    (FTensor L F -> Unit) >> Unit
  with
  | FPair A F l c => 
    fun f => f (FPair A F l c)
  end (Free Nat).
