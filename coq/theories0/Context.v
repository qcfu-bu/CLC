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

Inductive has {T} `{Ids T} `{Subst T} : seq_opt T -> nat -> T -> Prop :=
| has_O A Gamma :
  has (Some A :: Gamma) O A.[ren (+1)]
| has_S A B Gamma n : 
  has Gamma n A ->
  has (B :: Gamma) (S n) A.[ren (+1)].

Inductive all_none {T} : seq_opt T -> Prop :=
| nil_none : 
  all_none nil
| cons_none Delta : 
  all_none Delta ->
  all_none (None :: Delta).

Inductive only {T} `{Ids T} `{Subst T} : seq_opt T -> nat -> T -> Prop :=
| only_O A Delta : 
  all_none Delta ->
  only (Some A :: Delta) O A.[ren (+1)]
| only_S n Delta A : 
  only Delta n A ->
  only (None :: Delta) (S n) A.[ren (+1)].

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

Lemma only_not_none {T} `{Ids T} `{Subst T} Delta x A :
  only Delta x A -> all_none Delta -> False.
Proof.
  intros.
  dependent induction H1.
  - inversion H2.
  - inversion H2; eauto.
Qed.

Fixpoint pure T (Delta : seq_opt T) : seq_opt T :=
  match Delta with
  | _ :: Delta => None :: (pure Delta)
  | _ => nil
  end.

Lemma pure_all_none T (Delta : seq_opt T) :
  forall Delta', pure (Delta) = Delta' -> all_none Delta'.
Proof with eauto using all_none.
  induction Delta.
  - intros.
    inversion H.
    simpl.
    constructor.
  - intros.
    simpl in H.
    subst.
    constructor; eauto.
Qed.

Lemma all_none_pure T (Delta : seq_opt T) :
  all_none Delta -> pure Delta = Delta.
Proof.
  induction Delta; eauto.
  intros.
  inversion H; subst.
  simpl.
  rewrite IHDelta; eauto.
Qed.

Lemma only_pure {T} `{Ids T} `{Subst T} (Delta : seq_opt T) : 
  forall x A, only (pure Delta) x A -> False.
Proof.
  induction Delta.
  - intros.
    inversion H1.
  - intros.
    simpl in H1.
    inversion H1; subst.
    eapply IHDelta; eauto.
Qed.

Lemma has_pure {T} `{Ids T} `{Subst T} (Delta : seq_opt T) : 
  forall x A, has (pure Delta) x A -> False.
Proof.
  induction Delta.
  - intros.
    inversion H1.
  - intros.
    simpl in H1.
    inversion H1; subst.
    eapply IHDelta; eauto.
Qed.

Lemma pure_pure T (Delta : seq_opt T) :
  pure (pure Delta) = pure Delta.
Proof.
  induction Delta.
  - simpl; eauto.
  - simpl; eauto.
    rewrite IHDelta.
    eauto.
Qed.

Lemma only_has {T} `{Ids T} `{Subst T} (Delta : seq_opt T) x A :
  only Delta x A -> has Delta x A.
Proof.
  intros.
  induction H1.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma has_none {T} `{Ids T} `{Subst T} (Delta : seq_opt T) :
  ~ (exists x A, has Delta x A) -> all_none Delta.
Proof.
  induction Delta.
  - intros.
    constructor.
  - intros.
    destruct a.
    assert (exists x A, has (Some t :: Delta) x A).
    exists 0.
    exists (t.[ren (+1)]).
    constructor.
    contradiction.
    constructor.
    apply IHDelta.
    unfold not.
    intros.
    destruct H2.
    destruct H2.
    assert (exists x A, has (None :: Delta) x A).
    exists (x.+1).
    exists (x0.[ren (+1)]).
    constructor; eauto.
    contradiction.
Qed.

Lemma inv_merge T (Delta : seq_opt T) :
  exists Delta1 Delta2, merge Delta1 Delta2 Delta.
Proof.
  induction Delta.
  - exists nil.
    exists nil.
    constructor.
  - destruct IHDelta.
    destruct H.
    exists (a :: x).
    exists (None :: x0).
    constructor; eauto.
Qed.

Lemma all_none_merge_inv T (Delta : seq_opt T) :
  all_none Delta ->
  exists Delta1 Delta2,
    merge Delta1 Delta2 Delta /\
    all_none Delta1 /\
    all_none Delta2.
Proof.
  intro H.
  induction H.
  - exists nil.
    exists nil.
    firstorder; constructor.
  - firstorder.
    exists (None :: x).
    exists (None :: x0).
    firstorder; constructor; eauto.
Qed.
