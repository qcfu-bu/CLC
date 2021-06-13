Definition Loc : Type := Nat.

Definition Ptr : Type -> Linear := 
  fun A => (x : Loc * [x |-> A]).

Definition nbox : Ptr Nat := (alloc Nat 1).

Definition main : Nat := 
  let (l, c) := nbox in
  let (n, c) := get Nat l c in
  let c := set Nat Nat l c 2 in
  let (n, c) := get Nat l c in
  let _ := free Nat l c in
  n.


