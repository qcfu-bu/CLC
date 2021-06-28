Inductive Fin : Nat -> Type :=
| F1 : (n : Nat) -> Fin (S n)
| FS : (n : Nat) -> Fin n -> Fin (S n).

Inductive ArrVec (A : Type) (l : Loc) : Nat -> Linear :=
| Nil  : ArrVec A l 0
| Cons : (n : Nat) -> (add l n @ A) -> ArrVec A l n -> ArrVec A l (S n).

Definition Array (A : Type) (n : Nat) : Linear := [l : Loc | ArrVec A l n].

Fixpoint nth 
  (A : Type) 
  (l n : Nat) 
  (f : Fin n) 
  (v : ArrVec A l n) : 
  [A | ArrVec A l n] 
:=
  match f in Fin n return ArrVec A l n -> [A | ArrVec A l n] with
  | F1 n =>
    fun v =>
      match v in ArrVec _ _ n return
        match n with
        | O => Base
        | S _ => [A | ArrVec A l n]
        end
      with
      | Nil => ll
      | Cons n c v =>
        let [x, c] := Get A (add l n) c in
        [x, Cons n c v]
      end
  | FS n f =>
    fun v =>
      match v in ArrVec _ _ n return
        match n with
        | O => Base
        | S n => Fin n >> [A | ArrVec A l (S n)]
        end
      with
      | Nil => ll
      | Cons n c v => fun f =>
        let [x, v] := nth A l n f v in
        [x, Cons n c v]
      end f
  end v.

Definition index 
  (A : Type) 
  (n : Nat) 
  (f : Fin n) 
  (a : Array A n) :
  [A | Array A n]
:= 
  let [l, v] := a in
  let [x, v] := nth A l n f v in
  [x, [l, v]].


Definition Just0 : Type := (x : Nat | Eq Nat x 0).


Definition test 
  (n : Nat)
  (f : Fin n)
  (a : Array Just0 n) : 
  Array Just0 n
:= 
  let [x_pf, a] := index Just0 n f a in
  let [y_pf, a] := index Just0 n f a in
  let (x, pf1) := x_pf in
  let (y, pf2) := y_pf in
  let pf2 := Eq_sym Nat y 0 pf2 in
  let pf : Eq Nat x y := Eq_trans Nat x 0 y pf1 pf2 in
  a.

Definition main : Unit := ().
