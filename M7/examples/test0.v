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

Inductive Eq (A : Type) : A -> A -> Type :=
| Refl : (x : A) -> Eq A x x.

Inductive Sigma (A : Type) (F : A -> Type) : Type :=
| Pair : (x : A) -> F x -> Sigma A F.

Inductive Tensor (A : Linear) (B : Linear) : Linear :=
| TPair : A -> B -> Tensor A B.

Inductive FTensor (A : Type) (F : A -> Linear) : Linear :=
| FPair : (x : A) -> F x -> FTensor A F.

Inductive SN (N : Nat) : Type :=
| sn : (n : Nat) -> SN N.

Definition bad : SN (S O) := 
  sn (S O).


Definition Loc : Type := Nat.

Axiom PtsTo : Loc -> Type -> Linear.
Axiom New : (A : Type) -> A -> FTensor Loc (fun l => PtsTo l A).
Axiom Free : (A : Type) -> FTensor Loc (fun l => PtsTo l A) -> Unit.
Axiom Get : (A : Type) -> (l : Loc) -> PtsTo l A -> FTensor A (fun _ => PtsTo l A).
Axiom Set : (A : Type) -> (B : Type) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.

Definition prev (n : Nat) (x : SNat (S n)) : (SNat n) := 
  match x in SNat n return
    match n with
    | O => Unit
    | S n => SNat n
    end
  with
  | Zero => tt
  | Succ _ x => x
  end.

Definition main : Unit := 
  let ft := New Nat O in
  match ft in FTensor L F return 
    Unit
  with
  | FPair l c => Free Nat (FPair l c)
  end.
