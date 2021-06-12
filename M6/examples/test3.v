
Definition Loc : Type := Nat.

Definition Ptr : Type -> Linear := 
  fun A => (x : Loc * [x |-> A]).

Definition UL : Type := (Unit | Loc).
Definition nil : Type := 
  (x : UL * Eq(x, left (), UL)).
Definition cons : Loc -> Type := 
  fun l => (x : UL * Eq(x, right l, UL)).

(* fucking ridiculous *)
Definition LList : Nat -> Loc -> Linear := 
  fun n =>
    iter(
      fun _ => Loc -> Linear, 
      fun l => [l |-> nil],
      fun n LListn l => 
        (l' : Loc * ([l |-> cons l'] * (LListn l'))),
      n).

Definition List : (n : Nat) -> Linear := 
  fun n => (l : Loc * LList n l).
 
Definition Nil : List 0 := 
  alloc nil (left (), refl(left (), UL)).

Definition main : Unit := 
  free nil Nil.
