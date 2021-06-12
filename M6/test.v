Definition add : (Nat -> Nat -> Nat) := 
  fun x y =>
    iter(fun _ => Nat, y, fun _ x => S x, x).

Definition stdio : Channel := open 0.

Definition readClose : Channel -> Nat := 
  fun ch =>
    let (n, ch) := read ch in
    let _ := close ch in
    n.

Definition eq : Eq (readClose stdio, readClose stdio, Nat) :=
  refl(readClose stdio, Nat).

Definition main : Nat := add 1 2.
