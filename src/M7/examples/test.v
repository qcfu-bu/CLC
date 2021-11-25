Require Extraction.
Extraction Language Haskell.

Set Implicit Arguments.

Inductive le (n : nat) : nat -> Set :=
| le_n : le n n
| le_S : forall (m : nat), le n m -> le n (S m).

Definition lt (m n : nat) : Set := le (S m) n.

Inductive PtsTo (A : Set) : nat -> A -> Prop :=.

Axiom new  : forall (A : Set) (x : A), {l : nat | PtsTo l x}.
Axiom free : forall (A : Set)   (l : nat) {x : A}, PtsTo l x -> unit.
Axiom get  : forall (A : Set)   (l : nat) {x : A}, PtsTo l x -> {y : A | x = y} * PtsTo l x.
Axiom set  : forall (A B : Set) (l : nat) {x : A}, PtsTo l x -> forall (y : B), PtsTo l y.

Definition set_get (A B : Set) (l : nat) (x : A) (c : PtsTo l x) (y : B) : 
  let c := set c y in
  let (x_eq, c) := get c in
  let (x, eq) := x_eq in
  x = y.
Proof.
  intros.
  case (get c0).
  intros.
  case s.
  intros.
  rewrite e.
  reflexivity.
Qed.



Definition get_twice (A : Set) (l : nat) (x : A) (c : PtsTo A l x) :
  let (x_eq, c) := get A l c in
  let (x, eq1) := x_eq in
  let (y_eq, c) := get A l c in
  let (y, eq2) := y_eq in
  x = y.
Proof.
  case (get A l c).
  intros.
  case s.
  intros.
  case (get A l p).
  intros.
  case s0.
  intros.
  intuition.
Qed.

  refine (
    let p := get A l c in
    let H0 : get A l c = p := eq_refl in
    match get A l c as p0 return
      p = p0 ->
      let (x, c_pf1) := get A l c in
      let (c, pf1) := c_pf1 in
      let (y, c_pf2) := get A l c in
      let (c, pf2) := c_pf2 in
      x = y
    with 
    | (x, c_pf) => fun H1 => 
      match c_pf as c_pf0 return
        c_pf = c_pf0 ->
        let (x, c_pf1) := get A l c in
        let (c, pf1) := c_pf1 in
        let (y, c_pf2) := get A l c in
        let (c, pf2) := c_pf2 in
        x = y
      with
      | exist _ c pf => fun H2 => _
      end eq_refl
    end eq_refl).
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite <- pf.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Print get_twice.
  
  refine (
    let p0 := get A l c0 in
    let H2 : p0 = get A l c0 := eq_refl in
    _
  ).
  refine (
    match p0 as p1 return
      p0 = p1 -> 
      let (y, c_pf2) := get A l c0 in
      let (c, pf2) := c_pf2 in
      x = y
    with
    | (y, c_pf) => _
    end eq_refl
  ).

Proof.
  remember (get A l c).
  destruct p.
  destruct s.
  subst.
  rewrite <- Heqp.
  reflexivity.
Qed.



Inductive ArrVec (A : Set) (l : nat) : nat -> Prop :=
| Nil  : ArrVec A l 0
| Cons : forall (n : nat), (l + n @ A) -> ArrVec A l n -> ArrVec A l (S n).

Definition Array (A : Set) (n : nat) : Set := {l : nat | ArrVec A l n}.

Definition nth
  (A : Set) 
  (l m n : nat) 
  (pf : lt m n) 
  (v : ArrVec A l n) : 
  {c : l + m @ A | {c0 : l + m @ A | c = c0} -> {v0 : ArrVec A l n | v = v0}}.
Proof.
  induction pf.
  inversion v; subst.
  exists H0.
  intro pf.
  exists v.
  reflexivity.
  inversion v; subst.
  specialize (IHpf H1).
  destruct IHpf.
  exists x.
  intros.
  apply s in H.
  eauto.
Qed.



  refine(
  match pf in le _ n return
    ArrVec A l n -> 
    {c : l + m @ A | {c0 : l + m @ A | c = c0} -> {v0 : ArrVec A l n | v = v0}}
  with
  | le_n _ => _
  | le_S _ _ pf => _
  end v).
  refine(
  match pf in le _ n return
    ArrVec A l n -> 
    {c : l + m @ A | {c0 : l + m @ A | c = c0} -> {v0 : ArrVec A l n | v = v0}}
  with
  | le_n _ =>
    fun v =>
      match v in ArrVec _ _ n return
        match n with
        | O => IDProp
        | S n0 => 
          m = n0 -> 
          { c : l + n0 @ A | {c0 : l + n0 @ A | c = c0} -> {v0 : ArrVec A l n | v = v0} }
        end
      with
      | Nil _ _ => idProp
      | Cons _ _ n c v => _
      end eq_refl
  | le_S _ _ pf =>
    fun v =>
      match v in ArrVec _ _ n return 
        match n with
        | O => IDProp
        | S n0 => 
          lt m n0 -> 
          { c : l + m @ A | {c0 : l + m @ A | c = c0 } -> {v0 : ArrVec A l n | v = v0} }
        end
      with
      | Nil _ _ => idProp
      | Cons _ _ n c0 v0 => _
      end pf
  end v).

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