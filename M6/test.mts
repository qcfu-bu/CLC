Definition add : (Nat -> Nat -> Nat) := 
  fun x y =>
    iter(fun _ => Nat, y, fun _ x => S x, x).

Definition stdio : Channel := open 0.

Definition x : Nat := 
  let (n, stdio) := read stdio in
  let _ := close stdio in
  n.

Definition main : Nat := add 1 2.
