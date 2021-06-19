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

Definition Loc : Type := Nat.

Axiom PtsTo : Loc -> Type -> Linear.
Definition Ptr (A : Type) : Linear := FTensor Loc (fun l => PtsTo l A).

Axiom New  : (A : Type) -> A -> Ptr A.
Axiom Free : (A : Type) -> Ptr A -> Unit.
Axiom Get  : (A : Type) -> (l : Loc) -> PtsTo l A -> FTensor A (fun _ => PtsTo l A).
Axiom Set  : (A : Type) -> (B : Type) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.

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

Definition IO (A : Type) : Linear := 
  Ptr Nat >> FTensor A (fun _ => Ptr Nat).

Definition pure (A : Type) (x : A) : IO A := 
  fun ptr => FPair x ptr.

Definition bind (A : Type) (B : Type) : IO A >> (A >> IO B) >> IO B := 
  fun t1 f ptr => 
    let FPair x ptr := t1 ptr in
    f x ptr.




(* Definition bind (A : Type) (B : Type) : T A -> (A -> T B) := . *)



(* Definition n : Ptr Nat := New Nat O.

Definition Assign (A : Type) (x : A) (ptr : Ptr A) : Ptr A :=
  let FPair l c := ptr in
  let c := Set A A x l c in
  FPair l c. *)

Definition main : Nat := O.
  (* let FPair l c := n in
  let FPair x c := Get Nat l c in
  let _ := Free Nat (FPair l c) in
  x. *)
