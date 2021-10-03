
Definition set := nat -> bool.
Definition set_empty : set := fun _ => false.
Definition set_add (s : set) (n : nat) : set :=
  fun m =>
    orb (Nat.eqb m n) (s m).
Definition set_remove (s : set) (n : nat) : set :=
  fun m =>
    andb (negb (Nat.eqb m n)) (s m).

Definition map := nat -> option {A : Type & A}.
Definition map_empty : map := fun _ => None.
Definition map_add (s : map) (n : nat) (X : Set) (x : X) : map := 
  fun m =>
    if Nat.eqb m n
    then Some (existT (fun X => X) X x)
    else s m.
Definition map_remove (s : map) (n : nat) : map := 
  fun m =>
    if Nat.eqb m n
    then None 
    else s m.

Definition ptr (l : nat) (X : Type) (x : X) : Prop :=
  forall (s : map), (s l) = Some (existT (fun X => X) X x).

Definition T (X : Type) : Type := 
  map -> option (map * X).

Definition pure (X : Type) (x : X) : T X := 
  fun mem => Some (mem, x).

Definition bind 
  (A B : Type) 
  (c1 : T A) 
  (c2 : A -> T B) 
: T B := fun mem =>
  match c1 mem with
  | Some (mem, x) => c2 x mem
  | None => None
  end.
