Require Extraction.
Extraction Language Haskell.

Inductive le (n : nat) : nat -> Set :=
| le_n : le n n
| le_S : forall (m : nat), le n m -> le n (S m).

Definition lt (m n : nat) : Set := le (S m) n.

Inductive PtsTo (A : Set) : nat -> Prop :=.
Notation "l @ A" := (PtsTo A l) (at level 80, right associativity).

Axiom get : forall (A : Set) (l : nat), l @ A -> (A * (l @ A)).

Inductive ArrVec (A : Set) (l : nat) : nat -> Prop :=
| Nil  : ArrVec A l 0
| Cons : forall (n : nat), (l + n @ A) -> ArrVec A l n -> ArrVec A l (S n).

Definition Array (A : Set) (n : nat) : Set := {l : nat | ArrVec A l n}.

Fixpoint nth
  (A : Set) 
  (l m n : nat) 
  (pf : lt m n) 
  (v : ArrVec A l n) : 
  (l + m @ A) * ((l + m @ A) -> ArrVec A l n)
:=
  match pf in le _ n return
    ArrVec A l n -> 
    (l + m @ A) * ((l + m @ A) -> ArrVec A l n)
  with
  | le_n _ =>
    fun v =>
      match v in ArrVec _ _ n return
        match n with
        | O => IDProp
        | S n0 => m = n0 -> (l + n0 @ A) * ((l + n0 @ A) -> ArrVec A l n)
        end
      with
      | Nil _ _ => idProp
      | Cons _ _ n c v =>
        fun _ => ( c, fun c => Cons _ _ n c v )
      end eq_refl
  | le_S _ _ pf =>
    fun v =>
      match v in ArrVec _ _ n return 
        match n with
        | O => IDProp
        | S n0 => lt m n0 -> (l + m @ A) * ((l + m @ A) -> ArrVec A l n)
        end
      with
      | Nil _ _ => idProp
      | Cons _ _ n c0 v0 =>
        fun pf => 
          let ( c, f ) := nth A l m n pf v0 in
          ( c, fun c => Cons _ _ n c0 (f c) )
      end pf
  end v.

Definition Just0 : Type := {x : nat | x = 0}.

Definition index
  (A : Set) 
  (m n : nat) 
  (pf : lt m n) 
  (a : Array A n) : 
  (A * Array A n)
:=
  let (l, v) := a in
  let (c, f) := nth A l m n pf v in
  let (x, c0) := get A (l + m) c in
  (x, exist (fun l0 : nat => ArrVec A l0 n) l (f c0)).

Print index.

Extraction "index.hs" index.