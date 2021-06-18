Inductive Unit : Type :=
| tt : Unit.

Inductive Nat : Type :=
| O : Nat
| S : Nat -> Nat.

Inductive Sigma (A : Type) (F : A -> Type) : Type :=
| pair : (x : A) -> F x -> Sigma A F.

Inductive List (A : Type) : Type :=
| Nil : List A
| Cons : A -> List A -> List A.

Fixpoint len (A : Type) (ls : List A) : Nat :=
  match ls with
  | Nil => O
  | Cons _ ls => S (len A ls)
  end.

Definition main : Nat := 
  len Unit (Cons tt (Cons tt Nil)).
