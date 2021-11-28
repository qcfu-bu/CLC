
Inductive Box (A : U) : L :=
| box : A -> Box A.

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

Fixpoint len (A : U) (ls : list A) : Box nat :=
  match ls with
  | nil => box 0
  | cons h t => 
    let box x := len _ t in
    box (x + 1)
  end.

Definition ls1 : list nat := 
  cons 1 (cons 2 (cons 3 nil)).

Definition ls2 : list nat := 
  cons 4 (cons 5 (cons 6 nil)).

Definition main : nat := 
  let ls := append _ ls1 ls2 (fun x => x) in
  let box x := len _ ls in x.
