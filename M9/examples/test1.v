Axiom ptsto : (A : Type) -> Nat -> A -> Linear.

Axiom new  : (A : Type) -> (x : A) -> [l : Nat | ptsto _ l x].
Axiom free : (A : Type) -> (l : Nat) -> (x : A) -> ptsto _ l x -> Unit.
Axiom get  : (A : Type) -> (l : Nat) -> (x : A) -> ptsto _ l x -> 
  [(y : A | Eq _ x y) | ptsto _ l x].
Axiom set  : (A B : Type) -> (l : Nat) -> (x : A) -> ptsto _ l x ->
  (y : B) -> ptsto _ l y.

Definition main : Unit := 
  let [ _, c ] := new _ 1 in
  let [ xeq, c ] := get _ _ _ c in
  let [ yeq, c ] := get _ _ _ c in
  let ( x, pf1 ) := xeq in
  let ( y, pf2 ) := yeq in
  let pf1 := Eq_sym _ _ _ pf1 in
  let pf : Eq _ x y := Eq_trans _ _ _ _ pf1 pf2 in
  let c := set _ _ _ _ c 2 in
  let [ zeq, c ] := get _ _ _ c in
  let ( z, pf3 ) := zeq in
  let pf : Eq _ 2 z := pf3 in
  free _ _ _ c.
