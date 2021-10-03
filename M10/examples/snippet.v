
Module Type STATE.
  Parameter ptr : nat -> Prop.
  Parameter C : Type -> Type.
  Parameter pure : forall (A : Type), A -> C A.
  Parameter bind : forall (A B : Type), C A -> (A -> C B) -> C B.
  Parameter new : nat -> C {l : nat | ptr l}.
  Parameter free : forall (l : nat), ptr l -> C unit.
  Parameter get : forall (l : nat), ptr l -> C (nat * ptr l).
  Parameter set : forall (l : nat), ptr l -> nat -> C (ptr l).
  Parameter run : forall (A : Type), C A -> option A.
End STATE.

Module State : STATE.
  Definition ptr := ...
  Definition C := ...
  Definition pure := ...
  Definition bind := ...
  Definition new := ...
  Definition free := ...
  Definition get := ...
  Definition set := ...
  Definition run := ...
End State.

Import State.

Definition good0 : C nat := 
  { l, ptr } <- new 23 ;;
  ( n, ptr ) <- get ptr ;;
  _ <- free ptr ;;
  pure (n + n).
  
Compute good0.