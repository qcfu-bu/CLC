(** Length indexed Lists via linear pointers. *)

Definition Loc : Type := Nat.

Definition UL : Type -> Type := 
  fun A => (Unit | (A * Loc)).
Definition nil : Type -> Type := 
  fun A => (x : UL A * Eq(x, left (), UL A)).
Definition cons : Type -> Loc -> Type := 
  fun A l => (x : UL A * (a : A * Eq(x, right (a, l), UL A))).

Definition LList : Type -> Nat -> Loc -> Linear := 
  fun A n =>
    iter(
      fun _ => Loc -> Linear, 
      fun l => [l |-> nil A],
      fun n LListN l => (l' : Loc * ([l |-> cons A l'] * (LListN l'))),
      n).

Definition List : Type -> (n : Nat) -> Linear := 
  fun A n => (l : Loc * LList A n l).
 
Definition Nil : (A : Type) -> List A 0 := 
  fun A => alloc (nil A) (left (), refl(left (), UL A)).

Definition Cons : (A : Type) -> A -> (n : Nat) -> List A n -> List A (S n) :=
  fun A a _ ls =>
    let (l1, ls) := ls in
    let (l2, c) := alloc (cons A l1) 
      (right (a, l1), (a, refl(right (a, l1), UL A))) 
    in
    (l2, (l1, (c, ls))).

Definition Uncons : (A : Type) -> (n : Nat) -> List A (S n) -> List A n := 
  fun A _ ls => 
    let (l2, ls) := ls in
    let (l1, ls) := ls in
    let (c, ls) := ls in
    let _ := free (cons A l1) (l2, c) in
    (l1, ls).

Definition MakeList : (A : Type) -> A -> (n : Nat) -> List A n := 
  fun A a n => 
    iter(fun n => List A n, Nil A, fun n lsN => Cons A a n lsN, n).

Definition FreeList : (A : Type) -> (n : Nat) -> List A n -> Unit := 
  fun A n => 
    iter(
      fun n => List A n -> Unit,
      fun ls => free (nil A) ls,
      fun n FreeN ls =>
        let ls := Uncons A n ls in
        FreeN ls,
      n).

Definition main : Unit := ().