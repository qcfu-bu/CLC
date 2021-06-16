
Inductive Nat : Type :=
| O : Nat
| S : Nat -> Nat.

Inductive List : Type -> Type :=
| nil : (A : Type) -> List A
| cons : (A : Type) -> (A -> A) -> List A -> List A.

Fixpoint plus (x : Nat) (y : Nat) : Nat := 
  match x with
  | O => y
  | S x => S (plus x y)
  end.

Fixpoint count (A : Type) (ls : List A) : Nat :=
  match ls with
  | nil _ => O
  | cons _ _ ls => S (count A ls)
  end.

Fixpoint count' (A : Type) (ls : List A) : Nat :=
  match ls as x in List A return
    match A with
    | O => List A
    | S x => List x
    end
  with
  | nil _ => O
  | cons _ _ ls => S (count' A ls)
  end.

Definition ls : List Nat := 
  cons Nat O (nil Nat).

Definition main : Nat := 
  plus (plus (S O) (S O)) (count Nat ls).
