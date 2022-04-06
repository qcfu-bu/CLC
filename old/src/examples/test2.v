Inductive list (A : U) : L :=
| nil : list A
| cons : A -> list A -> list A.

Fixpoint append (A : U) : 
  list A -o list A -o (list A -o list A) -o list A :=
  fun ls1 ls2 k =>
    match ls1 with
    | nil => k ls2
    | cons h t => 
      let _cons_ : A -o list A -o list A := 
        fun h t => cons h t 
      in
      append _ t ls2 (fun res => k (_cons_ h res))
    end.

Fixpoint len (A : U) (ls : list A) : [ nat | list A ] :=
  match ls with
  | nil => [ 0 , nil ]
  | cons hd tl =>
    let [ n, tl ] := len _ tl in
    [ n + 1, cons hd tl ]
  end.

Fixpoint free (A : U) (ls : list A) : unit :=
  match ls with
  | nil => ()
  | cons h t => free _ t
  end.

Definition ls1 : list nat := 
  cons 1 (cons 2 (cons 3 nil)).

Definition ls2 : list nat := 
  cons 4 (cons 5 (cons 6 nil)).

Definition main : unit := 
  let ls := append _ ls1 ls2 (fun x => x) in
  let [ n, ls ] := len _ ls in
  free _ ls.