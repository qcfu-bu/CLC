(* Capabilities are computationally irrelevant. *)

Definition Loc : Type := Nat.

Definition Ref : Type -> Linear := 
  fun A => (x : Loc * [x |-> A]).

Definition New : (A : Type) -> A -> Ref A := 
  fun A x => alloc A x.

Definition Get : (A : Type) -> Ref A -> (A * Ref A) := 
  fun A ref => 
    let (l, c) := ref in
    let (x, c) := get A l c in
    (x, (l, c)).

(* Subtlty wrong in arrow type of codomain.
   Definition Assign : (A : Type) -> Ref A -> A -> Ref A := 
     fun A ref _ =>
       let (l, c) := ref in
       (l, c). *)

Definition Assign : (A : Type) -> Ref A -> A >> Ref A := 
  fun A ref x =>
    let (l, c) := ref in
    let c := set A A l c x in
    (l, c).

Definition Free : (A : Type) -> Ref A -> Unit := 
  fun A ref => 
    let (l, c) := ref in free A l c.

Definition main : (Nat * (Nat * Nat)) := 
  let ref := New Nat 1 in
  let (m, ref) := Get Nat ref in
  let ref := Assign Nat ref 2 in
  let (n, ref) := Get Nat ref in
  (* Variables m, n are fully abstract, they cannot be proven equal.
     let pf : Eq(m, n, Nat) := refl(n, Nat) in *)
  let _ := Free Nat ref in
  (m, (n, n)).