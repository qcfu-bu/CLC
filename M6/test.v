Definition add : (Nat -> Nat -> Nat) := 
  fun x y =>
    iter(fun _ => Nat, y, fun _ x => S x, x).

Definition stdin : Channel := open 0.
Definition stdout: Channel := open 0.

Definition readClose : Channel >> Nat := 
  fun ch =>
    let (n, ch) := read ch in
    let _ : Unit := close ch in
    n.

Definition adversary : ((Channel >> Nat) -> (Channel * Channel) -> Nat) :=
  fun f x =>
    let (x1, x2) := x in
    let n1 := f x1 in
    let n2 := f x2 in
    add n1 n2.

Definition main : Nat := 
  adversary readClose (stdin, stdout).