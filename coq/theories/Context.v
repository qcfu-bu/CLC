(** * Context

    Support for dependent contexts with the right reduction behaviour. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import AutosubstSsr.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition seq_opt T := seq (option T).
Definition cons_Some T (n : T) (Delta : seq_opt T) : seq_opt T := 
  Some n :: Delta.

Inductive all_none T : seq_opt T -> Prop :=
| nil_none : 
  all_none nil
| cons_none Delta : 
  all_none Delta ->
  all_none (None :: Delta).

Inductive only T : seq_opt T -> nat -> T -> Prop :=
| only_O A Delta : 
  all_none Delta ->
  only (Some A :: Delta) O A
| only_S n Delta A : 
  only Delta n A ->
  only (None :: Delta) (S n) A.

Inductive merge T : seq_opt T -> seq_opt T -> seq_opt T -> Prop :=
| merge_empty :
  merge nil nil nil
| merge_consL n Delta1 Delta2 Delta :
  merge Delta1 Delta2 Delta ->
  merge (n :: Delta1) (None :: Delta2) (n :: Delta)
| merge_consR n Delta1 Delta2 Delta :
  merge Delta1 Delta2 Delta ->
  merge (None :: Delta1) (n :: Delta2) (n :: Delta).

Notation "n ::: Delta" := (cons_Some n Delta) (at level 50).

Fixpoint merge_ T (Delta1 Delta2 : seq_opt T) : seq_opt T :=
  match Delta1, Delta2 with
  | nil, nil => nil
  | n :: Delta1, None :: Delta2 => n :: (merge_ Delta1 Delta2)
  | None :: Delta1, n :: Delta2 => n :: (merge_ Delta1 Delta2)
  | _, _ => nil
  end.

Lemma merge_ok T (Delta1 Delta2 Delta : seq_opt T) :
  merge Delta1 Delta2 Delta ->
    Delta = merge_ Delta1 Delta2.
Proof with eauto.
  intros.
  induction H...
  - destruct n; simpl; subst...
  - destruct n; simpl; subst...
Qed.

Definition get {T} `{Ids T} (Gamma : seq T) (n : var) : T :=
  nth (ids 0) Gamma n.
Arguments get {T _} Gamma n.

Fixpoint dget {T} `{Ids T} `{Subst T} (Gamma : list T) (n : var) {struct n} : T :=
  match Gamma, n with
    | [::], _ => ids 0
    | A :: _, 0 => A.[ren (+1)]
    | _ :: Gamma, n.+1 => (dget Gamma n).[ren (+1)]
  end.
Arguments dget {T _ _} Gamma n.

Lemma get_map {T} `{Ids T} (f : T -> T) Gamma n :
  n < size Gamma -> get (map f Gamma) n = f (get Gamma n).
Proof. exact: nth_map. Qed.