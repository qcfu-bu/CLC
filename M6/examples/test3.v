(** Length indexed Lists via linear pointers. *)

Definition Loc : Type := Nat.

Definition null : Type := Unit.
Definition box : Type -> Loc -> Type := 
  fun A l => (a : A * (l' : Loc * Eq(l, l', Loc))).

Definition LList : Type -> Nat -> Loc -> Linear := 
  fun A n =>
    iter(
      fun _ => Loc -> Linear, 
      fun l => [l |-> null],
      fun n LListN l => (l' : Loc * ([l |-> box A l'] * (LListN l'))),
      n).

Definition List : Type -> (n : Nat) -> Linear := 
  fun A n => (l : Loc * LList A n l).
 
Definition Nil : (A : Type) -> List A 0 := 
  fun A => alloc (null) ().

Definition Cons : (A : Type) -> A -> (n : Nat) -> List A n -> List A (S n) :=
  fun A a _ ls =>
    let (l1, ls) := ls in
    let (l2, c) := alloc (box A l1) (a, (l1, refl(l1, Loc))) in
    (l2, (l1, (c, ls))).

Definition Uncons : (A : Type) -> (n : Nat) -> List A (S n) -> (A * (List A n)) := 
  fun A _ ls => 
    let (l2, ls) := ls in
    let (l1, ls) := ls in
    let (c, ls) := ls in
    let (bx, c) := get (box A l1) l2 c in
    let _ := free (box A l1) l2 c in
    let (a, _) := bx in
    (a, (l1, ls)).

Definition MakeList : (A : Type) -> A -> (n : Nat) -> List A n := 
  fun A a n => 
    iter(fun n => List A n, Nil A, fun n lsN => Cons A a n lsN, n).

Definition FreeList : (A : Type) -> (n : Nat) -> List A n -> Unit := 
  fun A n => 
    iter(
      fun n => List A n -> Unit,
      fun ls => 
        let (l, ls) := ls in 
        free null l ls,
      fun n FreeN ls =>
        let (_, ls) := Uncons A n ls in
        FreeN ls,
      n).

Definition main : Unit := 
  let x := MakeList Nat 1 10 in
  let _ := FreeList Nat 10 x in 
  ().