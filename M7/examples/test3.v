Definition lnId (A : Type) : Linear := A >> A.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m => S (add m n)
  end.

Inductive Fin : Nat -> Type :=
| F1 : (n : Nat) -> Fin (S n)
| FS : (n : Nat) -> Fin n -> Fin (S n).

Inductive ArrVec (A : Type) (l : Loc) : Nat -> Linear :=
| Nil  : ArrVec A l 0
| Cons : (n : Nat) -> (add l n @ A) -> ArrVec A l n -> ArrVec A l (S n).

Definition Array (A : Type) (n : Nat) : Linear := [l : Loc | ArrVec A l n].

Definition First (A : Type) (n : Nat) (arr : Array A (S n)) : [A | Array A (S n)] := 
  let [l, v] := arr in
  match v in ArrVec _ _ n1 return
    match n1 with
    | O => Eq Nat n n >> lnId A
    | S n2 => Eq Nat n2 n >> [A | Array A (S n)]
    end
  with
  | Nil => fun _ x => x
  | Cons n1 c v => 
    fun pf =>
      let f1 : Nat -> Linear := fun n => add l n @ A in
      let f2 : Nat -> Linear := fun n => ArrVec A l n in
      let c := LnInd Nat n1 n f1 pf c in
      let v := LnInd Nat n1 n f2 pf v in
      let [x, c] := Get A (add l n) c in
      [x, [l, Cons n c v]]
  end refl.


Definition main : Unit := ().
