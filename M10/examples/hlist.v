Require Import List.
Set Implicit Arguments.

Definition heapTy := list (option Type).

Inductive heap : heapTy -> Type :=
| hnil : heap nil
| hsome {X : Type} {Xs : heapTy} (x : X) : 
  heap Xs -> heap (Some X :: Xs)
| hnone {Xs : heapTy} : 
  heap Xs -> heap (None :: Xs).

Notation "[;;]" := (hnil).
Notation "h ;; t" := (hsome h t)
  (at level 30, right associativity).

Fixpoint hget 
  {Xs : heapTy} 
  (h : heap Xs)
  (n : nat) 
: match nth n Xs None with
  | Some ty => option ty
  | None    => option Empty_set
  end :=
  match n with
  | O =>
    match h in heap Xs return
      match nth 0 Xs None with
      | Some ty => option ty
      | None    => option Empty_set
      end
    with 
    | hnil => None
    | hsome x _ => Some x
    | hnone _ => None
    end
  | S n => 
    match h in heap Xs return
      match nth (S n) Xs None with
      | Some ty => option ty
      | None    => option Empty_set
      end
    with
    | hnil => None
    | hsome _ mls => hget mls n
    | hnone mls => hget mls n
    end
  end.

Fixpoint alloc (h : heapTy) (X : Type) : heapTy :=
  match h with
  | Some _ :: h => alloc h X
  | None :: _ => Some X :: h
  | nil => Some X :: nil
  end.

Inductive C : 
  Type -> list (option Type) -> list (option Type) -> Type :=
| pure Xs X (x : X) : C X Xs Xs
| bind Xs Ys Zs A B : C A Xs Ys -> (A -> C B Ys Zs) -> C B Xs Zs.

Fixpoint run 
  {Xs Ys : list (option Type)}
  {X : Type}
  (c : C X Xs Ys) 
  (mem : mlist Xs) 
: option (X * mlist Ys) :=
  match c in C X Xs Ys return 
    mlist Xs -> option (X * mlist Ys)
  with
  | pure _ x => fun mem => 
    Some (x, mem)
  | bind c1 c2 => fun mem => 
    match run c1 mem with
    | Some (x, mem) => run (c2 x) mem
    | None => None
    end
  end mem.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
  (at level 30, right associativity).