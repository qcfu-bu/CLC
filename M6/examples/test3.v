(** Length indexed Lists via linear pointers. *)

Definition Loc : Type := Nat.

Definition UL : Type := (Unit | Loc).
Definition nil : Type := (x : UL * Eq(x, left (), UL)).
Definition cons : Loc -> Type := fun l => (x : UL * Eq(x, right l, UL)).

Definition LList : Nat -> Loc -> Linear := 
  fun n =>
    iter(
      fun _ => Loc -> Linear, 
      fun l => [l |-> nil],
      fun n LListN l => (l' : Loc * ([l |-> cons l'] * (LListN l'))),
      n).

Definition List : (n : Nat) -> Linear := 
  fun n => (l : Loc * LList n l).
 
Definition Nil : Unit -> List 0 := 
  fun _ => alloc nil (left (), refl(left (), UL)).

Definition Cons : (n : Nat) -> List n -> List (S n) :=
  fun _ ls =>
    let (l1, ls) := ls in
    let (l2, c) := alloc (cons l1) (right l1, refl(right l1, UL)) in
    (l2, (l1, (c, ls))).
 
Definition Uncons : (n : Nat) -> List (S n) -> List n := 
  fun _ ls => 
    let (l2, ls) := ls in
    let (l1, ls) := ls in
    let (c, ls) := ls in
    let _ := free (cons l1) (l2, c) in
    (l1, ls).

Definition FreeList : (n : Nat) -> List n -> Unit := 
  fun n => 
    iter(
      fun n => List n -> Unit,
      fun ls => free nil ls,
      fun n FreeN ls =>
        let ls := Uncons n ls in
        FreeN ls,
      n).

Definition main : Unit := 
  let ls := Cons 1 (Cons 0 (Nil ())) in
  FreeList 2 ls.