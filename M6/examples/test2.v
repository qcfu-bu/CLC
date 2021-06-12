
Definition Ptr : Type -> Linear := 
  fun A => (x : Nat * [x |-> A]).

Definition nbox : Ptr Nat := (alloc Nat 1).

Definition main : Nat := 
  let (n, nbox) := get Nat nbox in
  let _ := free Nat nbox in
  n.


