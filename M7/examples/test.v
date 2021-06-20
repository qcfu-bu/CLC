Inductive le (n : nat) : nat -> Type :=
| le_n : le n n.
(* | le_S : forall (m : nat), le n m -> le n (S m). *)

Definition lt (m n : nat) : Type := le (S m) n.

Inductive PtsTo (A : Type) : nat -> Type :=.
Notation "l @ A" := (PtsTo A l) (at level 80, right associativity).


Inductive ArrVec (A : Type) (l : nat) : nat -> Type :=
| Nil  : ArrVec A l 0
| Cons : forall (n : nat), (l + n @ A) -> ArrVec A l n -> ArrVec A l (S n).

Fixpoint nth
  (A : Type) 
  (l m n : nat) 
  (pf : lt m n) 
  (v : ArrVec A l n) : 
  (l + m @ A) * ((l + m @ A) -> ArrVec A l n)
:=
  match pf in le _ n return
    ArrVec A l n -> 
    (add l m @ A) ^ ((add l m @ A) >> ArrVec A l n)
  with
  | le_n =>
    fun v =>
      match v in ArrVec _ _ n return
        match n with
        | O => Base
        | S n0 => Eq Nat m n0 >> (add l m @ A) ^ ((add l m @ A) >> ArrVec A l n)
        end
      with
      | Nil => ll
      | Cons n c v =>
        fun pf => 
          let f1 : Nat -> Linear := fun n => add l n @ A in
          let f2 : Nat -> Linear := fun n => ArrVec A l n in
          let c := LnInd Nat m n f1 pf c in
          let v := LnInd Nat m n f2 pf v in
          { c, fun c => Cons n c v }
      end refl
  end v.


Definition main : Unit := ().

