Definition id (A : U) : A -o A :=
  fun x => x.

Definition main : unit := 
  let x := id nat 5 in
  ().