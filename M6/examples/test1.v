(* Capabilities are computationally irrelevant. *)

Definition Loc : Type := Nat.

Definition Ptr : Type -> Linear := 
  fun A => (x : Loc * [x |-> A]).

Definition Alloc : (A : Type) -> A -> Ptr A := 
  fun A x => alloc A x.

Definition Get : (A : Type) -> Ptr A -> (A * Ptr A) := 
  fun A ptr => 
    let (l, c) := ptr in
    let (x, c) := get A l c in
    (x, (l, c)).

(* Subtlety in arrow type of codomain.
   Definition Assign : (A : Type) -> Ptr A -> A -> Ptr A := 
     fun A ptr _ =>
       let (l, c) := ptr in
       (l, c). *)

Definition Set : (A : Type) -> Ptr A -> A >> Ptr A := 
  fun A ptr x =>
    let (l, c) := ptr in
    let c := set A A l c x in
    (l, c).

Definition Free : (A : Type) -> Ptr A -> Unit := 
  fun A ptr => 
    let (l, c) := ptr in free A l c.

Definition main : (Nat * Nat) := 
  let ptr := Alloc Nat 1 in
  let (m, ptr) := Get Nat ptr in
  let ptr := Set Nat ptr 2 in
  let (n, ptr) := Get Nat ptr in
  (* Variables m, n are fully abstract, they cannot be proven equal.
     let pf : Eq(m, n, Nat) := refl(n, Nat) in *)
  let _ := Free Nat ptr in
  (m, n).