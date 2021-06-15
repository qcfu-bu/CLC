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

Definition main : 
  (let ref := New Nat 2 in
   let ref := Assign Nat ref 1 in
   let _ := Free Nat ref in
   Nat)
:= 7.
