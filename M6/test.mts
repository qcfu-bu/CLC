Definition add : (Nat -> Nat -> Nat) := fun x y =>
  iter(fun _ => Nat, y, fun _ x => S x, x)