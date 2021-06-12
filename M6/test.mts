Definition add : (Nat -> Nat -> Nat) := 
  fun x y =>
    iter(fun _ => Nat, y, fun _ x => S x, x).

Definition main : Nat := add 1 2.
