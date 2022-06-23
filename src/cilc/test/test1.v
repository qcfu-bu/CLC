Axiom ptsto : forall (A : U), nat -> A -> L.

Axiom new  : forall (A : U) (x : A), [l : nat | ptsto _ l x].
Axiom free : (A : U) -> (l : nat) -> (x : A) -> ptsto _ l x -> unit.
Axiom get  : (A : U) -> (l : nat) -> (x : A) -> ptsto _ l x -> 
  [(y : A | eq _ x y) | ptsto _ l x].
Axiom set  : (A B : U) -> (l : nat) -> (x : A) -> ptsto _ l x ->
  (y : B) -> ptsto _ l y.

Definition main : unit := 
  let [ _, c ] := new _ 1 in
  let [ xeq, c ] := get _ _ _ c in
  let [ yeq, c ] := get _ _ _ c in
  let ( x, pf1 ) := xeq in
  let ( y, pf2 ) := yeq in
  let pf1 := eq_sym _ _ _ pf1 in
  let pf : eq _ x y := eq_trans _ _ _ _ pf1 pf2 in
  let c := set _ _ _ _ c 2 in
  let [ zeq, c ] := get _ _ _ c in
  let ( z, pf3 ) := zeq in
  let pf : eq _ 2 z := pf3 in
  free _ _ _ c.
