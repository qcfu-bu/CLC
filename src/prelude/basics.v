Inductive eq (A : U) (x : A) : A -> U :=
| refl : eq A x x.

Definition eq_trans
  (A : U)
  (x y z : A)
  (e1 : eq A x y)
  (e2 : eq A y z) :
  eq A x z
:=
  match e2 in eq _ _ y return eq A x y with
  | refl => e1
  end.

Definition eq_sym 
  (A : U) 
  (x y : A) 
  (e : eq A x y) :
  eq A y x
:=
  match e in eq _ _ y return eq A y x with
  | refl => refl
  end.

Definition u_ind 
  (A : U) 
  (x y : A)
  (P : A -> U) 
  (e : eq A x y)
  (f : P x) :
  P y
:= 
  match e in eq _ _ y return P y with
  | refl => f
  end.

Definition l_ind 
  (A : U) 
  (x y : A)
  (P : A -> L) 
  (e : eq A x y)
  (f : P x) :
  P y
:= 
  match e in eq _ _ y return P y with
  | refl => f
  end.

Inductive unit : U :=
| tt : unit.

Inductive base : L :=
| ll : base.

Inductive nat : U :=
| O : nat
| S : nat -> nat.

Fixpoint add (m n : nat) : nat :=
  match m with
  | O => n
  | S m => S (add m n)
  end.

Inductive bool : U :=
| true : bool
| false : bool.

Inductive sigma (A : U) (F : A -> U) : U :=
| pair : (x : A) -> F x -> sigma A F.

Inductive tensor (A : L) (B : L) : L :=
| tpair : A -> B -> tensor A B.

Inductive ftensor (A : U) (F : A -> L) : L :=
| fpair : (x : A) -> F x -> ftensor A F.

Axiom unsafeC : (A : L) -> A -> unit.
Axiom unsafeP : (A : L) -> A.

Definition Loc : U := nat.
Axiom PtsTo : Loc -> U -> L.
Definition Ptr (A : U) : L := ftensor Loc (fun l => PtsTo l A).
Axiom New  : (A : U) -> A -> Ptr A.
Axiom Free : (A : U) -> Ptr A -> unit.
Axiom Get  : (A : U) -> (l : Loc) -> PtsTo l A -> ftensor A (fun _ => PtsTo l A).
Axiom Set  : (A : U) -> (B : U) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.
