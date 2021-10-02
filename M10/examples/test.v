Require Import List.
Set Implicit Arguments.

Module Type StateSig.
  Parameter ptr : nat -> Prop.
  Parameter C : Type -> Type.
  Parameter pure : forall (A : Type), A -> C A.
  Parameter bind : forall (A B : Type), C A -> (A -> C B) -> C B.
  Parameter new : nat -> C {l : nat | ptr l}.
  Parameter free : forall (l : nat), ptr l -> C unit.
  Parameter get : forall (l : nat), ptr l -> C (nat * ptr l).
  Parameter set : forall (l : nat), ptr l -> nat -> C (ptr l).
  Parameter run : forall (A : Type), C A -> option A.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
    (at level 30, right associativity).
  Notation "{ l , ptr } <- c1 ;; c2" := 
    (bind c1 (fun x => 
      match x with
      | exist _ l ptr => c2
      end)) 
    (at level 30, right associativity).
  Notation "( n , ptr ) <- c1 ;; c2" := 
    (bind c1 (fun x => 
      match x with
      | (n, ptr) => c2
      end))
    (at level 30, right associativity).
End StateSig.

Module State <: StateSig.

Definition mem := list (option nat).

Inductive ptrT : nat -> Prop :=
| loc l : ptrT l.

Definition ptr := ptrT.

Definition C (A : Type) : Type := mem -> option (mem * A).
Definition pure (A : Type) (a : A) : C A :=
  fun mem => Some (mem, a).
Definition bind (A B : Type) (c1 : C A) (c2 : A -> C B) : C B :=
  fun mem => 
    match c1 mem with 
    | Some (mem, a) => c2 a mem
    | None => None
    end.

Definition new (n : nat) : C {l : nat | ptr l} := fun mem =>
  let fix aux mem l := 
    match mem with 
    | Some x :: mem => 
      match aux mem (S l) with
      | Some (mem, res) => Some (Some x :: mem, res)
      | None => None
      end
    | None :: mem => 
      let mem := Some n :: mem in
      let res := exist (fun l => ptr l) l (loc l) in
      Some (mem, res)
    | nil => 
      let mem := Some n :: nil in
      let res := exist (fun l => ptr l) l (loc l) in
      Some (mem, res)
    end
  in aux mem 0.

Definition free (l : nat) (c : ptr l) : C unit := fun mem =>
  let fix aux mem l :=
    match mem, l with
    | Some _ :: mem, O => Some (None :: mem, tt)
    | None :: _, O => None
    | h :: mem, S l =>
      match aux mem l with
      | Some (mem, res) => Some (h :: mem, res)
      | None => None
      end
    | nil, _ => None
    end
  in 
  aux mem l.

Definition get (l : nat) (c : ptr l) : C (nat * ptr l) := fun mem =>
  let fix aux mem l :=
    match mem, l with
    | Some n :: _, O => Some (mem, (n, c))
    | None :: _, O => None
    | h :: mem, S l' =>
      match aux mem l' with
      | Some (mem, res) => Some (h :: mem, res)
      | None => None
      end
    | nil, _ => None
    end
  in aux mem l.

Definition set (l : nat) (c : ptr l) (m : nat) : C (ptr l) := fun mem =>
  let fix aux mem l :=
    match mem, l with
    | Some _ :: mem, O => Some (Some m :: mem, loc l)
    | None :: _, O => None
    | h :: mem, S l' =>
      match aux mem l' with
      | Some (mem, res) => Some (h :: mem, loc l)
      | None => None
      end
    | nil, _ => None
    end
  in aux mem l.

Definition run (A : Type) (c : C A) : option A := 
  let fix aux (mem : mem) (res : A) :=
    match mem with
    | Some _ :: _ => None
    | None :: mem => aux mem res
    | nil => Some res
    end
  in
  match c nil with  
  | Some (mem, res) => aux mem res
  | None => None
  end.

End State.

Module Test (M : StateSig).

Import M.

Definition good0 : C nat := 
  { l, ptr } <- new 23 ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  pure (n + n).

Definition good1 : C nat := 
  { l, ptr } <- new 23 ;;
  ( m, ptr ) <- get ptr ;;
  ptr <- set ptr 32 ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  pure (n + m).

Definition good2 : C nat := 
  { l1, ptr1 } <- new 23 ;;
  { l2, ptr2 } <- new 32 ;;
  ( n1, ptr1 ) <- get ptr1 ;;
  ( n2, ptr2 ) <- get ptr2 ;;
  _ <- free ptr1 ;;
  _ <- free ptr2 ;;
  pure (n1 + n2).

Definition bad0 : C nat := 
  { l, ptr } <- new 23 ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  _ <- free ptr ;;
  pure (n + n).

Definition bad1 : C nat := 
  { l, ptr } <- new 23 ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  ( n, ptr ) <- get ptr ;;
  pure (n + n).

Definition bad2 : C nat := 
  { l, ptr } <- new 23 ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  ptr <- set ptr 32 ;;
  pure (n + n).

Definition bad3 : C nat := 
  _ <- new 23 ;;
  pure 0.

Definition bad4 : C nat := 
  { l, ptr } <- new 23 ;;
  { l, ptr } <- new 32 ;;
  ( m, ptr ) <- get ptr ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  pure (m + n).

End Test.

Module Import TestState := Test(State).
Compute (State.run good0).
Compute (State.run good1).
Compute (State.run good2).
Compute (State.run bad0).
Compute (State.run bad1).
Compute (State.run bad2).
Compute (State.run bad3).
Compute (State.run bad4).