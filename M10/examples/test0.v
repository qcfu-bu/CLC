Inductive le (n : Nat) : Nat -> Type :=
| le_n : le n n
| le_S : (m : Nat) -> le n m -> le n (S m).

Definition lt (m n : Nat) : Type := le (S m) n.

Inductive ArrVec (A : Type) (l : Loc) : Nat -> Linear :=
| Nil  : ArrVec A l 0
| Cons : (n : Nat) -> (A @ l + n) -> ArrVec A l n -> ArrVec A l (S n).

Definition Array (A : Type) (n : Nat) : Linear := [l : Loc | ArrVec A l n].

(* proof irrelevant traversal of ArrVec *)
Fixpoint nth 
  (A : Type) 
  (l m n : Nat) 
  (pf : lt m n) 
  (v : ArrVec A l n) : 
  (A @ l + m) ^ ((A @ l + m) >> ArrVec A l n)
:=
  match pf in le _ n return
    ArrVec A l n -> (A @ l + m) ^ ((A @ l + m) >> ArrVec A l n)
  with
  | le_n =>
    fun v =>
      match v in ArrVec _ _ n return
        match n with
        | O => Base
        | S n0 => Eq Nat m n0 >> (A @ l + n0) ^ ((A @ l + n0) >> ArrVec A l n)
        end
      with
      | Nil => ll
      | Cons n c v =>
        fun _ => { c, fun c => Cons n c v }
      end refl
  | le_S _ pf =>
    fun v =>
      match v in ArrVec _ _ n return 
        match n with
        | O => Base
        | S n0 => lt m n0 >> (A @ l + m) ^ ((A @ l + m) >> ArrVec A l n)
        end
      with
      | Nil => ll
      | Cons n c0 v0 =>
        fun pf => 
          let { c, f } := nth A l m n pf v0 in
          { c, fun c => Cons n c0 (f c) }
      end pf
  end v.

(* safe array indexing *)
Definition index 
  (A : Type) 
  (m n : Nat) 
  (pf : lt m n) 
  (a : Array A n) :
  [A | Array A n]
:= 
  let [ l, v ] := a in
  let { c, f } := nth _ l m n pf v in
  let [ x, c ] := Get _ (l + m) c in
  [x, [l, f c]].


Definition Just0 : Type := (x : Nat | Eq Nat x 0).


Definition silly (m n : Nat) (pf : lt m n) (a : Array Just0 n) : Array Just0 n := 
  let [x_pf, a] := index Just0 _ _ pf a in
  let [y_pf, a] := index Just0 _ _ pf a in
  let (x, pf1) := x_pf in
  let (y, pf2) := y_pf in
  let pf2 := Eq_sym Nat y 0 pf2 in
  let pf : Eq Nat x y := Eq_trans Nat x 0 y pf1 pf2 in
  a.

Definition main : Unit := ().

