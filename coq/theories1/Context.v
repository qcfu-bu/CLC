(** * Context

    Support for dependent contexts with the right reduction behaviour. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import AutosubstSsr.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive elem T :=
| Left  of T
| Right of T
| Null.

Definition context T := seq (elem T).
Definition cons_Left T (n : T) (Gamma : context T) : context T := 
  Left n :: Gamma.
Definition cons_Right T (n : T) (Gamma : context T) : context T := 
  Right n :: Gamma.
Definition cons_Null T (Gamma : context T) : context T := 
  (Null _) :: Gamma.

Notation "m :L Gamma" := (cons_Left m Gamma) (at level 30).
Notation "m :R Gamma" := (cons_Right m Gamma) (at level 30).
Notation ":N Gamma" := (cons_Null Gamma) (at level 30).

Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  merge nil nil nil
| merge_left Gamma1 Gamma2 Gamma m : 
  merge Gamma1 Gamma2 Gamma ->
  merge (m :L Gamma1) (m :L Gamma2) (m :L Gamma)
| merge_right1 Gamma1 Gamma2 Gamma m :
  merge Gamma1 Gamma2 Gamma ->
  merge (m :R Gamma1) (:N Gamma2) (m :R Gamma)
| merge_right2 Gamma1 Gamma2 Gamma m :
  merge Gamma1 Gamma2 Gamma ->
  merge (:N Gamma1) (m :R Gamma2) (m :R Gamma)
| merge_null Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  merge (:N Gamma1) (:N Gamma2) (:N Gamma).

Inductive pure T : context T -> Prop :=
| pure_nil :
  pure nil
| pure_L Gamma m : 
  pure Gamma ->
  pure (m :L Gamma)
| pure_N Gamma : 
  pure Gamma ->
  pure (:N Gamma).

Inductive hasL {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| hasL_O m Gamma :
  pure Gamma ->
  hasL (m :L Gamma) 0 m.[ren (+1)]
| hasL_S Gamma v m n : 
  hasL Gamma v m ->
  hasL (n :L Gamma) (v.+1) m.[ren (+1)]
| hasL_N Gamma v m : 
  hasL Gamma v m ->
  hasL (:N Gamma) (v.+1) m.[ren (+1)].

Inductive hasR {T} `{Ids T} `{Subst T} :
  context T -> var -> T -> Prop :=
| hasR_O m Gamma :
  pure Gamma ->
  hasR (m :R Gamma) 0 m.[ren (+1)]
| hasR_S Gamma v m n :
  hasR Gamma v m ->
  hasR (n :L Gamma) (v.+1) m.[ren (+1)]
| hasR_N Gamma v m :
  hasR Gamma v m ->
  hasR (:N Gamma) (v.+1) m.[ren (+1)].

Fixpoint re T (Gamma : context T) : context T :=
  match Gamma with
  | Left m :: Gamma => Left m :: re Gamma
  | _ :: Gamma => Null _ :: re Gamma
  | _ => nil
  end.

Lemma re_re T (Gamma : context T) :
  re Gamma = re (re Gamma).
Proof.
  induction Gamma.
  - simpl.
    reflexivity.
  - case a; intros; simpl.
    rewrite <- IHGamma.
    reflexivity.
    rewrite <- IHGamma.
    reflexivity.
    rewrite <- IHGamma.
    reflexivity.
Qed.

Lemma pure_re T (Gamma : context T) :
  pure Gamma -> Gamma = re Gamma.
Proof.
  induction Gamma; intros.
  - eauto.
  - inv H; simpl.
    rewrite <- IHGamma; eauto.
    rewrite <- IHGamma; eauto.
Qed.

Lemma re_pure T (Gamma : context T) : pure (re Gamma).
Proof.
  induction Gamma; intros.
  constructor.
  destruct a; simpl; constructor; eauto.
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A -> hasL (re Gamma) x A.
Proof.
  induction 1; simpl.
  - constructor.
    rewrite <- pure_re; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma hasL_pure {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A -> pure Gamma.
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma hasL_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A ->
  forall B,
    hasL Gamma x B ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasL in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasL in H5. rewrite H5; eauto.
Qed.

Lemma hasR_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasR Gamma x A ->
  forall B,
    hasR Gamma x B ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasR in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasR in H5. rewrite H5; eauto.
Qed.

Lemma hasL_hasR {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A ->
  forall B,
    ~ hasR Gamma x B.
Proof.
  induction 1; unfold not; intros.
  inv H2.
  inv H2; apply IHhasL in H7; eauto.
  inv H2; apply IHhasL in H5; eauto.
Qed.
