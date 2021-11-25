
Inductive list (A : Type) : Linear :=
| nil : list A
| cons : A -> list A -> list A.

Fixpoint append (A : Type) : 
  list A >> list A >> (list A >> list A) >> list A :=
  fun ls1 ls2 k =>
    match ls1 with
    | nil => k ls2
    | cons h t => 
      let _cons_ : A >> list A >> list A := 
        fun h t => cons h t 
      in
      append _ t ls2 (fun res => k (_cons_ h res))
    end.

Fixpoint len (A : Type) (ls : list A) : Nat :=
  match ls with
  | nil => 0
  | cons h t => 
    1 + len _ t
  end.

Definition ls1 : list Nat := 
  cons 1 (cons 2 (cons 3 nil)).

Definition ls2 : list Nat := 
  cons 4 (cons 5 (cons 6 nil)).

Definition main : Nat := 
  let ls := append _ ls1 ls2 (fun x => x) in
  len _ ls.
