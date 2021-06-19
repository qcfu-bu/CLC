Inductive Fin : Nat -> Type :=
| F1 : (n : Nat) -> Fin (S n)
| FS : (n : Nat) -> Fin n -> Fin (S n).

Inductive Vec (A : Type) : Nat -> Type :=
| Nil  : Vec A 0
| Cons : (n : Nat) -> A -> Vec A n -> Vec A (S n).

Fixpoint nth (A : Type) (n : Nat) (x : Fin n) (v : Vec A n) : A :=
  match x in Fin n return Vec A n -> A with
  | F1 n => 
    fun v =>
      match v in Vec _ n return 
        match n with
        | O => Unit
        | S _ => A
        end
      with
      | Nil => ()
      | Cons _ x _ => x
      end
  | FS n x =>
    fun v =>
      match v in Vec _ n return 
        match n with
        | O => Unit
        | S n => Fin n -> A 
        end
      with
      | Nil => ()
      | Cons n _ v => fun x => nth A n x v
      end x
  end v.

Definition main : Unit := ().