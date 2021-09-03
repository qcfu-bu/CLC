Axiom ptsto : (A : Type) -> Nat -> A -> Linear.

Axiom new : (A : Type) -> (x : A) -> ptsto _ 0 x.

Definition main : Unit := tt.
