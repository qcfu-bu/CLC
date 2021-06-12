Definition tyId : (A : Type) -> A -> A := 
  fun A x => x.

Definition lnId : (A : Linear) -> A -> A :=
  fun A x => x.

Definition add : (Nat -> Nat -> Nat) := 
  fun x y =>
    iter(fun _ => Nat, y, fun _ x => S x, x).

Definition ch1 : Channel := open 0.
Definition ch2 : Channel := open 0.
Definition ch3 : Channel := open 1.


Definition readClose : Channel -> Nat := 
  fun ch =>
    let (n, ch) := read ch in
    let _ : Unit := close ch in
    n.

Definition adversary : ((Channel -> Nat) -> (Channel * Channel) -> Nat) :=
  fun f x =>
    let (x1, x2) := x in
    let n1 := f x1 in
    let n2 := f x2 in
    add n1 n2.

Definition main : Unit := 
  let n := adversary readClose (ch1, ch2) in
  let ch3 := write (n, ch3) in
  close ch3.