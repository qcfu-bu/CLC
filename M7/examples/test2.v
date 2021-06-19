Definition lnId (A : Type) : Linear := A >> A.

Inductive Le : Nat -> Nat -> Type :=
| LtO : (n : Nat) -> Le n n
| LtS : (m n : Nat) -> Le m n -> Le m (S n).

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (add m n)
  end.

Inductive ArrVec (A : Type) (l : Loc) : Nat -> Linear :=
| Nil  : ArrVec A l 0
| Cons : (n : Nat) -> (add l n @ A) -> ArrVec A l n -> ArrVec A l (S n).

Definition Lt (m n : Nat) : Type := Le (S m) n.

Definition Array (A : Type) (n : Nat) : Linear := [l : Loc | ArrVec A l n].
Definition First (A : Type) (n : Nat) (arr : Array A (S n)) : [A | Array A (S n)] := 
  let [l, v] := arr in
  match v in ArrVec _ _ n return
    match n with
    | O => lnId A
    | S n => [A | Array A (S n)]
    end
  with
  | Nil => fun x => x
  | Cons n c v =>
    let [x, c] := Get A (add l n) c in
    [x, [l, Cons n c v]]
  end.

Definition main : Unit := ().