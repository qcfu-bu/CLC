(* Capabilities are computationally irrelevant. *)

Definition Loc : Type := Nat.

Definition Ptr : Type -> Linear := 
  fun A => (x : Loc * [x |-> A]).

Definition nbox : Ptr Nat := (alloc Nat 1).

Definition main : (Nat * Nat) := 
  let (l, c) := nbox in
  let (m, c) := get Nat l c in
  let c := set Nat Nat l c 2 in
  let (n, c) := get Nat l c in
  (* Variables m, n are fully abstract, they cannot be proven equal.
     let pf : Eq(m, n, Nat) := refl(n, Nat) in *)
  let _ := free Nat l c in
  (m, n).