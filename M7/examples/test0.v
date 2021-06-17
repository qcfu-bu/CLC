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

Definition neg (b : Bool) : Bool := 
  match b with  
  | true => false
  | false => true
  end.

Fixpoint add (x : Nat) (y : Nat) : Nat :=
  match x with
  | O => y
  | S x => S (add x y)
  end.

Definition pred (n : Nat) (x : SNat (S n)) : SNat n := 
  match x in SNat n return
    match n with
    | O => Unit
    | S n => SNat n
    end
  with
  | Zero => tt
  | Succ _ x => x
  end.

Definition One : SNat (S O) := Succ O Zero.

Definition main : SNat O := pred O One.
