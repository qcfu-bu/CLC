From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program.
Require Import AutosubstSsr ARS coc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DLTT.

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

Inductive ithR {T} : context T -> nat -> Prop :=
| ithR_O m Gamma :
  ithR (m :R Gamma) 0
| ithR_S Gamma n e :
  ithR Gamma n ->
  ithR (e :: Gamma) n.+1.

Inductive ithL {T} : context T -> nat -> Prop :=
| ithL_O m Gamma :
  ithL (m :L Gamma) 0
| ithL_S Gamma n e :
  ithL Gamma n ->
  ithL (e :: Gamma) n.+1.

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

Lemma ithR_pure T (Gamma : context T) n :
  ithR Gamma n -> ~ pure Gamma.
Proof.
  unfold not.
  intros.
  induction H.
  inv H0.
  inv H0; eauto.
Qed.

Lemma hasR_ithR {T} `{Ids T} `{Subst T} (Gamma : context T) A n :
  hasR Gamma n A -> forall m, ithR Gamma m -> m = n.
Proof.
  induction 1; intros.
  - inv H2; eauto.
    exfalso; eapply ithR_pure; eauto.
  - inv H2.
    erewrite <- IHhasR; eauto.
  - inv H2.
    erewrite <- IHhasR; eauto.
Qed.

Lemma merge_sym T (Gamma1 Gamma2 Gamma : context T) : 
  merge Gamma1 Gamma2 Gamma ->
  merge Gamma2 Gamma1 Gamma.
Proof.
  induction 1; intros; constructor; eauto.
Qed.

Lemma merge_pure_inv T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  pure Gamma -> pure Gamma1 /\ pure Gamma2.
Proof.
  induction 1; intros; constructor; eauto.
  - inv H0.
    constructor; firstorder.
  - inv H0.
    constructor; firstorder.
  - inv H0.
  - inv H0.
  - inv H0.
  - inv H0.
  - inv H0.
    constructor; firstorder.
  - inv H0.
    constructor; firstorder.
Qed.

Lemma merge_pure1 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  pure Gamma1 -> Gamma = Gamma2.
Proof.
  induction 1; intros; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_pure2 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  pure Gamma2 -> Gamma = Gamma1.
Proof.
  induction 1; intros; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H0.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_pure_pure T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  pure Gamma1 -> pure Gamma2 -> pure Gamma.
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    constructor; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    constructor; eauto.
Qed.

Lemma merge_pure_eq T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  pure Gamma1 -> pure Gamma2 -> Gamma1 = Gamma2.
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_re_re T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  re Gamma1 = re Gamma /\ re Gamma2 = re Gamma.
Proof.
  induction 1; simpl; intros; eauto; firstorder.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H0; eauto.
  rewrite H1; eauto.
Qed.

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

Lemma hasR_re {T} `{Ids T} `{Subst T} (Gamma : context T) :
  forall x A, ~hasR (re Gamma) x A.
Proof.
  induction Gamma; unfold not; intros.
  - simpl in H1. inv H1.
  - destruct a; simpl in H1; inv H1; eapply IHGamma; eauto.
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

Lemma merge_split1 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Gamma1 ->
    exists Delta,
      merge Delta1 Gamma2 Delta /\
      merge Delta Delta2 Gamma.
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m :L x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m :R x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (:N x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m :R x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (:N x).
    repeat constructor; eauto.
Qed.

Lemma merge_split2 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Gamma1 ->
    exists Delta,
      merge Delta2 Gamma2 Delta /\
      merge Delta1 Delta Gamma.
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m :L x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (:N x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m :R x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m :R x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (:N x).
    repeat constructor; eauto.
Qed.

Inductive sort : Type := U | L.

Inductive term : Type :=
| Var    (x : var)
| Sort   (srt : sort) (l : nat)
| TyProd (A : term) (B : {bind term}) (s : sort)
| LnProd (A : term) (B : {bind term}) (s : sort)
| Arrow  (A B : term) (s : sort)
| Lolli  (A B : term) (s : sort)
| Lam    (n : {bind term})
| App    (m n : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort srt l   : value (Sort srt l)
| value_var x        : value (Var x)
| value_tyProd A B s : value (TyProd A B s)
| value_lnProd A B s : value (LnProd A B s)
| value_arrow A B s  : value (Arrow A B s)
| value_lolli A B s  : value (Lolli A B s)
| value_lam n        : value (Lam n).

Definition v_subst (sigma : var -> term) : Prop := 
  forall x, value (sigma x).

Lemma ren_v_subst n : v_subst (ren (+ n)).
Proof with eauto using value.
  unfold v_subst.
  intros.
  induction x...
Qed.

Lemma ids_v_subst : v_subst ids.
Proof with eauto using value.
  unfold v_subst.
  intros.
  induction x...
Qed.

Lemma value_v_subst n :
  value n -> v_subst (n .: ids).
Proof with eauto using value.
  unfold v_subst.
  intros.
  induction x...
Qed.

Lemma value_subst v :
  value v ->
    forall sigma,
      v_subst sigma ->
      value v.[sigma].
Proof with eauto using value.
  intros.
  dependent induction H...
Qed.

Lemma v_subst_up sigma :
  v_subst sigma -> v_subst (up sigma).
Proof with eauto using value.
  unfold v_subst.
  intros.
  induction x; asimpl...
  apply value_subst...
  unfold v_subst...
Qed.

Lemma v_subst_cons sigma v :
  v_subst sigma -> value v -> v_subst (v .: sigma).
Proof.
  unfold v_subst.
  intros.
  induction x; asimpl; eauto.
Qed.

Inductive step : term -> term -> Prop :=
| step_beta n v :
  value v ->
  step (App (Lam n) v) (n.[v/])
| step_appL m m' n :
  step m m' ->
  step (App m n) (App m' n)
| step_appR v n n' :
  value v ->
  step n n' ->
  step (App v n) (App v n').

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort srt l :
  pstep (Sort srt l) (Sort srt l)
| pstep_lam n n' : 
  pstep n n' -> 
  pstep (Lam n) (Lam n')
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta n n' v v' :
  pstep n n' ->
  value v ->
  pstep v v' ->
  pstep (App (Lam n) v) (n'.[v'/])
| pstep_tyProd A A' B B' s :
  pstep A A' ->
  pstep B B' ->
  pstep (TyProd A B s) (TyProd A' B' s)
| pstep_lnProd A A' B B' s :
  pstep A A' ->
  pstep B B' ->
  pstep (LnProd A B s) (LnProd A' B' s)
| pstep_arrow A A' B B' s : 
  pstep A A' ->
  pstep B B' ->
  pstep (Arrow A B s) (Arrow A' B' s)
| pstep_lolli A A' B B' s : 
  pstep A A' ->
  pstep B B' ->
  pstep (Lolli A B s) (Lolli A' B' s).

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.

Lemma step_pstep n n' : step n n' -> pstep n n'.
Proof with eauto using pstep, pstep_refl.
  intros.
  induction H...
Qed.

Lemma pstep_value v v' : pstep v v' -> value v -> value v'.
Proof.
  intros.
  dependent induction H; eauto using value.
  inv H1.
  inv H2.
Qed.

Lemma red_value v v' : red v v' -> value v -> value v'.
Proof.
  induction 1; eauto.
  intros.
  specialize (IHstar H1).
  eapply pstep_value; eauto.
Qed.

Lemma pstep_subst s t : 
  pstep s t -> 
    forall sigma, 
      v_subst sigma -> 
      pstep s.[sigma] t.[sigma].
Proof with eauto using pstep, pstep_refl.
  intros.
  dependent induction H...
  - asimpl. 
    apply pstep_lam.
    apply IHpstep.
    apply v_subst_up...
  - asimpl.
    pose proof (v_subst_up H2).
    specialize (IHpstep1 _ H3).
    specialize (IHpstep2 _ H2).
    pose proof (value_subst H0 H2).
    pose proof (pstep_beta IHpstep1 H4 IHpstep2).
    asimpl in H5...
  - asimpl.
    pose proof (v_subst_up H1).
    pose proof (IHpstep1 _ H1).
    pose proof (IHpstep2 _ H2)...
  - asimpl.
    pose proof (v_subst_up H1).
    pose proof (IHpstep1 _ H1).
    pose proof (IHpstep2 _ H2)...
Qed.

Lemma red_subst s t : 
  red s t -> 
    forall sigma, 
      v_subst sigma -> 
      red s.[sigma] t.[sigma].
Proof.
  induction 1; intros.
  eauto.
  eapply star_trans.
  apply IHstar; eauto.
  econstructor; eauto.
  apply pstep_subst; eauto.
Qed.

Definition psstep (sigma tau : var -> term) := 
  forall x, pstep (sigma x) (tau x).

Lemma psstep_refl sigma : psstep sigma sigma.
Proof with eauto using pstep_refl.
  unfold psstep.
  induction x...
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
  unfold v_subst.
  induction x; eauto using value.
Qed.

Lemma psstep_v_subst sigma tau :
  psstep sigma tau -> v_subst sigma -> v_subst tau.
Proof.
  unfold v_subst. unfold psstep. intros.
  induction x.
  - pose proof (H0 0).
    pose proof (H 0).
    eapply pstep_value; eauto.
  - pose proof (H0 x.+1).
    pose proof (H x.+1).
    eapply pstep_value; eauto.
Qed.

Lemma pstep_compat s t :
  pstep s t ->
    forall sigma tau, 
      v_subst sigma ->
      psstep sigma tau -> pstep s.[sigma] t.[tau].
Proof with eauto 6 using pstep, psstep_up, v_subst_up.
  intros.
  dependent induction H; asimpl...
  - pose proof (v_subst_up H2).
    pose proof (psstep_up H3).
    pose proof (IHpstep1 _ _ H4 H5).
    pose proof (IHpstep2 _ _ H2 H3).
    pose proof (psstep_v_subst H3 H2).
    pose proof (value_subst H0 H2).
    pose proof (pstep_beta H6 H9 H7).
    asimpl in H10...
Qed.

Lemma psstep_compat s1 s2 sigma tau:
  psstep sigma tau -> pstep s1 s2 -> psstep (s1 .: sigma) (s2 .: tau).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' ->
  value n ->
  pstep m.[n/] m.[n'/].
Proof with eauto using pstep, pstep_refl.
  intros.
  apply pstep_compat...
  - eauto using value_v_subst.
  - apply psstep_compat...
    apply psstep_refl.
Qed.

Lemma pstep_compat_beta m m' :
  pstep m m' -> 
    forall n n',
      pstep n n' ->
      value n ->
      pstep m.[n/] m'.[n'/].
Proof with eauto using psstep_refl, psstep_compat, value_v_subst.
  intros.
  apply pstep_compat...
Qed.

Ltac first_order :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : ex2 _ _ |- _ ] => destruct H
  | [ H1 : ?A -> _, H2 : ?A |- _ ] => specialize (H1 H2)
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ |- _ /\ _ ] => split
  end.

Lemma pstep_diamond m m1 :
  pstep m m1 ->
  forall m2, pstep m m2 ->
    exists m', pstep m1 m' /\ pstep m2 m'.
Proof with eauto using pstep.
  intros.
  dependent induction H.
  - inv H0. exists (Var x)...
  - inv H0. exists (Sort srt l)...
  - inv H0. apply (IHpstep) in H2. first_order. exists (Lam x)...
  - inv H1.
    + apply (IHpstep1) in H4. apply (IHpstep2) in H6. first_order.
      exists (App x0 x)...
    + inv H. 
      assert (pstep (Lam n0) (Lam n'0))...
      pose proof (pstep_value H7 H5). 
      pose proof (pstep_value H0 H5).
      apply (IHpstep1) in H. apply (IHpstep2) in H7. first_order.
      inv H.
      inv H7.
      exists (n'2.[x0/]). split.
      apply pstep_beta...
      apply pstep_compat_beta...
  - inv H2.
    + inv H5.
      pose proof (pstep_value H7 H0).
      apply IHpstep2 in H7. apply IHpstep1 in H3. first_order.
      exists (x.[x0/]). split.
      * apply pstep_compat_beta...
        eapply pstep_value; eauto.
      * apply pstep_beta...
    + pose proof (pstep_value H8 H6).
      apply IHpstep1 in H5. apply IHpstep2 in H8. first_order.
      exists (x0.[x/]). split.
      * apply pstep_compat_beta...
        eapply pstep_value; eauto.
      * apply pstep_compat_beta...
  - inv H1. apply (IHpstep1) in H6. apply (IHpstep2) in H7.
    first_order. exists (TyProd x0 x s)...
  - inv H1. apply (IHpstep1) in H6. apply (IHpstep2) in H7.
    first_order. exists (LnProd x0 x s)...
  - inv H1. apply (IHpstep1) in H6. apply (IHpstep2) in H7.
    first_order. exists (Arrow x0 x s)...
  - inv H1. apply (IHpstep1) in H6. apply (IHpstep2) in H7.
    first_order. exists (Lolli x0 x s)...
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> red m m2 ->
    exists m', red m1 m' /\ pstep m2 m'.
Proof with eauto using pstep_refl, star.
  intros.
  dependent induction H0... first_order.
  pose proof (pstep_diamond H1 H3). first_order.
  exists x0. split...
Qed.

Theorem confluence :
  confluent pstep.
Proof with eauto using pstep_refl, star.
  unfold confluent.
  unfold joinable.
  intros.
  dependent induction H.
  - exists z; eauto.
  - first_order.
    pose proof (strip H0 H2). first_order.
    exists x1; eauto.
    eapply star_trans.
    apply H3.
    apply star1; eauto.
Qed.
Hint Resolve confluence.

Theorem church_rosser :
  CR pstep.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.
Hint Resolve church_rosser.

Lemma conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> A B. apply: (conv_trans (App m' n)).
  - apply: (conv_hom (App^~ n)) A => x y ps. 
    constructor; eauto.
    apply pstep_refl.
  - apply: conv_hom B => x y ps.
    constructor; eauto.
    apply pstep_refl.
Qed.

Lemma conv_lam s1 s2 : s1 === s2 -> Lam s1 === Lam s2.
Proof. apply: conv_hom => x y. exact: pstep_lam. Qed.

Lemma conv_tyProd s A A' B B' :
  A === A' -> B === B' -> TyProd A B s === TyProd A' B' s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (TyProd A' B s)).
  - apply: (conv_hom ((TyProd^~ B)^~ s)) conv1 => x y ps.
    constructor; eauto.
    apply pstep_refl.
  - apply: (conv_hom ((TyProd A')^~ s)) conv2 => x y ps.
    constructor; eauto.
    apply pstep_refl.
Qed.

Lemma conv_lnProd s A A' B B' :
  A === A' -> B === B' -> LnProd A B s === LnProd A' B' s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (LnProd A' B s)).
  - apply: (conv_hom ((LnProd^~ B)^~ s)) conv1 => x y ps.
    constructor; eauto.
    apply pstep_refl.
  - apply: (conv_hom ((LnProd A')^~ s)) conv2 => x y ps.
    constructor; eauto.
    apply pstep_refl.
Qed.

Lemma conv_arrow s A A' B B' :
  A === A' -> B === B' -> Arrow A B s === Arrow A' B' s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Arrow A' B s)).
  - apply: (conv_hom ((Arrow^~ B)^~ s)) conv1 => x y ps.
    constructor; eauto.
    apply pstep_refl.
  - apply: (conv_hom ((Arrow A')^~ s)) conv2 => x y ps.
    constructor; eauto.
    apply pstep_refl.
Qed.

Lemma conv_lolli s A A' B B' :
  A === A' -> B === B' -> Lolli A B s === Lolli A' B' s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Lolli A' B s)).
  - apply: (conv_hom ((Lolli^~ B)^~ s)) conv1 => x y ps.
    constructor; eauto.
    apply pstep_refl.
  - apply: (conv_hom ((Lolli A')^~ s)) conv2 => x y ps.
    constructor; eauto.
    apply pstep_refl.
Qed.

Lemma conv_subst sigma s t : 
  v_subst sigma ->
  s === t -> s.[sigma] === t.[sigma].
Proof. 
  intro H.
  apply conv_hom. 
  intros.
  apply pstep_subst; eauto.
Qed.

Lemma sort_ren_inv s l v xi :
  Sort s l = v.[ren xi] -> v = Sort s l.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma var_ren_inv x v xi :
  Var x = v.[ren xi] -> exists n, v = Var n.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma tyProd_ren_inv A B s v xi :
  TyProd A B s = v.[ren xi] -> exists A' B' s', v = TyProd A' B' s'.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma lnProd_ren_inv A B s v xi :
  LnProd A B s = v.[ren xi] -> exists A' B' s', v = LnProd A' B' s'.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma arrow_ren_inv A B s v xi :
  Arrow A B s = v.[ren xi] -> exists A' B' s', v = Arrow A' B' s'.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma lolli_ren_inv A B s v xi :
  Lolli A B s = v.[ren xi] -> exists A' B' s', v = Lolli A' B' s'.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma lam_ren_inv m v xi :
  Lam m = v.[ren xi] -> exists n, v = Lam n.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma value_rename xi A :
  value A <-> value A.[ren xi].
Proof.
  split.
  induction 1; asimpl; constructor.
  intros.
  dependent induction H.
  apply sort_ren_inv in x; subst.
  constructor.
  apply var_ren_inv in x.
  inv x.
  constructor.
  apply tyProd_ren_inv in x; first_order; subst; constructor.
  apply lnProd_ren_inv in x; first_order; subst; constructor.
  apply arrow_ren_inv in x; first_order; subst; constructor.
  apply lolli_ren_inv in x; first_order; subst; constructor.
  apply lam_ren_inv in x; inv x; constructor.
Qed.

Definition left_invertible (f : nat -> nat) := 
  exists g, g ∘ f = id.

Lemma left_invertible_upren xi :
  left_invertible xi -> left_invertible (upren xi).
Proof.
  unfold left_invertible.
  intros.
  inv H.
  exists (upren x).
  assert (upren x ∘ upren xi = upren xi >>> upren x) by autosubst.
  rewrite H; asimpl.
  replace (xi >>> x) with (x ∘ xi) by autosubst.
  rewrite H0; autosubst.
Qed.

Lemma pstep_ren_inv m n xi :
  pstep m.[ren xi] n ->
  left_invertible xi ->
    exists x, pstep m x /\ x.[ren xi] = n.
Proof.
  intro H.
  dependent induction H; intros.
  - inv H.
    exists ((Var x0).[ren x1]).
    rewrite x; asimpl.
    replace (xi >>> x1) with (x1 ∘ xi) by autosubst.
    rewrite H0; asimpl; firstorder.
    apply pstep_refl.
  - exists m; firstorder.
    apply pstep_refl.
  - destruct m; asimpl; try discriminate.
    inversion H0.
    inv x.
    assert (n0.[up (ren xi)] = n0.[ren (upren xi)]) by autosubst.
    apply left_invertible_upren in H0.
    pose proof (IHpstep n0 (upren xi) H2 H0).
    inv H3. inv H4.
    exists (Lam x); asimpl; firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m1.[ren xi] = m1.[ren xi]) by eauto.
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    apply IHpstep1 in H2; eauto.
    apply IHpstep2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (App x1 x).
    firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    destruct m1; asimpl; try discriminate. inv H4.
    assert (n0.[up (ren xi)] = n0.[ren (upren xi)]) by autosubst.
    pose proof (left_invertible_upren H2).
    pose proof (IHpstep1 n0 (upren xi) H3 H4).
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    pose proof (IHpstep2 m2 xi H6 H2).
    firstorder; subst; asimpl.
    exists (x1.[x .: ids]); asimpl.
    firstorder.
    constructor; eauto.
    apply <- value_rename; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m.[ren xi] = m.[ren xi]) by eauto.
    assert (B0.[up (ren xi)] = B0.[ren (upren xi)]) by autosubst.
    assert (left_invertible (upren xi)).
    apply left_invertible_upren; eauto.
    apply IHpstep1 in H2; eauto.
    apply IHpstep2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (TyProd x0 x1 s0); asimpl; firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m.[ren xi] = m.[ren xi]) by eauto.
    assert (B0.[up (ren xi)] = B0.[ren (upren xi)]) by autosubst.
    assert (left_invertible (upren xi)).
    apply left_invertible_upren; eauto.
    apply IHpstep1 in H2; eauto.
    apply IHpstep2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (LnProd x0 x1 s0); asimpl; firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m1.[ren xi] = m1.[ren xi]) by eauto.
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    apply IHpstep1 in H2; eauto.
    apply IHpstep2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (Arrow x1 x s0); asimpl; firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m1.[ren xi] = m1.[ren xi]) by eauto.
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    apply IHpstep1 in H2; eauto.
    apply IHpstep2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (Lolli x1 x s0); asimpl; firstorder.
    constructor; eauto.
Qed.

Lemma pstep_ren1_inv m n :
  pstep m.[ren (+1)] n ->
    exists x, pstep m x /\ x.[ren (+1)] = n.
Proof.
  intros.
  apply pstep_ren_inv; eauto.
  unfold left_invertible.
  exists (predn).
  autosubst.
Qed.

Lemma red_sort_inv s l A :
  red (Sort s l) A -> A = (Sort s l).
Proof.
  induction 1; intros; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_tyProd_inv A B x s :
  red (TyProd A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = TyProd A' B' s.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order.
    rewrite H3 in H0.
    inv H0.
    exists A'.
    exists B'.
    repeat constructor; eauto using star.
Qed.

Lemma red_lnProd_inv A B x s :
  red (LnProd A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = LnProd A' B' s.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order.
    rewrite H3 in H0.
    inv H0.
    exists A'.
    exists B'.
    repeat constructor; eauto using star.
Qed.

Lemma red_arrow_inv A B x s :
  red (Arrow A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Arrow A' B' s.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order.
    rewrite H3 in H0.
    inv H0.
    exists A'.
    exists B'.
    repeat constructor; eauto using star.
Qed.

Lemma red_lolli_inv A B x s :
  red (Lolli A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Lolli A' B' s.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order.
    rewrite H3 in H0.
    inv H0.
    exists A'.
    exists B'.
    repeat constructor; eauto using star.
Qed.

Lemma red_var_inv x y :
  red (Var x) y -> y = Var x.
Proof.
  induction 1; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_lam_inv m n :
  red (Lam m) n ->
  exists m',
    red m m' /\ n = Lam m'.
Proof.
  induction 1.
  - exists m; repeat constructor.
  - first_order; subst.
    inv H0.
    exists n'.
    repeat constructor; eauto using star.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  Sort s1 l1 === Sort s2 l2 ->
  s1 = s2 /\ l1 = l2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_sort_inv in H0.
  apply red_sort_inv in H1.
  first_order; subst; inv H1; eauto.
Qed.

Lemma tyProd_inj A1 A2 B1 B2 s1 s2 :
  TyProd A1 B1 s1 === TyProd A2 B2 s2 ->
  A1 === A2 /\ B1 === B2 /\ s1 = s2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_tyProd_inv in H0.
  apply red_tyProd_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
Qed.

Lemma lnProd_inj A1 A2 B1 B2 s1 s2 :
  LnProd A1 B1 s1 === LnProd A2 B2 s2 ->
  A1 === A2 /\ B1 === B2 /\ s1 = s2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_lnProd_inv in H0.
  apply red_lnProd_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
Qed.

Lemma arrow_inj A1 A2 B1 B2 s1 s2 :
  Arrow A1 B1 s1 === Arrow A2 B2 s2 ->
  A1 === A2 /\ B1 === B2 /\ s1 = s2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_arrow_inv in H0.
  apply red_arrow_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
Qed.

Lemma lolli_inj A1 A2 B1 B2 s1 s2 :
  Lolli A1 B1 s1 === Lolli A2 B2 s2 ->
  A1 === A2 /\ B1 === B2 /\ s1 = s2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_lolli_inv in H0.
  apply red_lolli_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
Qed.

Ltac red_inv m H :=
  match m with
  | Var    => apply red_var_inv in H
  | Sort   => apply red_sort_inv in H
  | TyProd => apply red_tyProd_inv in H
  | LnProd => apply red_lnProd_inv in H
  | Arrow  => apply red_arrow_inv in H
  | Lolli  => apply red_lolli_inv in H
  | Lam    => apply red_lam_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : red (?m _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _) _ |- _ ] => red_inv m H
  end;
  first_order; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  | [ H : value (App _ _) |- _ ] => inv H
  end; eauto.

Inductive sub1 : term -> term -> Prop :=
| sub1_refl A : 
  sub1 A A
| sub1_sort s l1 l2 : 
  l1 <= l2 -> 
  sub1 (Sort s l1) (Sort s l2)
| sub1_tyProd A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (TyProd A B1 s) (TyProd A B2 s)
| sub1_lnProd A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (LnProd A B1 s) (LnProd A B2 s)
| sub1_arrow A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (Arrow A B1 s) (Arrow A B2 s)
| sub1_lolli A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (Lolli A B1 s) (Lolli A B2 s).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : 
  sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 30, no associativity).

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_sort s n m : n <= m -> Sort s n <: Sort s m.
Proof. move=> leq. exact/sub1_sub/sub1_sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto 6 using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D => {A B}
    [ A C D | s l1 l2 leq C D conv sb
    | A B1 B2 s sb1 ih C D conv sb2
    | A B1 B2 s sb1 ih C D conv sb2
    | A B1 B2 s sb1 ih C D conv sb2
    | A B1 B2 s sb1 ih C D conv sb2 ]...
  - inv sb...
    + move: conv => /sort_inj [->eq].
      apply: sub_sort. subst.
      exact: leq_trans leq _.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
  - inv sb2...
    + exfalso; solve_conv.
    + move: conv => /tyProd_inj[conv1 [conv2 ->] ].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_tyProd... eapply conv_tyProd... exact: conv_tyProd.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
  - inv sb2...
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + move: conv => /lnProd_inj[conv1 [conv2 ->] ].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_lnProd... eapply conv_lnProd... exact: conv_lnProd.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
  - inv sb2...
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + move: conv => /arrow_inj[conv1 [conv2 ->] ].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_arrow... eapply conv_arrow... exact: conv_arrow.
    + exfalso; solve_conv.
  - inv sb2...
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + move: conv => /lolli_inj[conv1 [conv2 ->] ].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_lolli... eapply conv_lolli... exact: conv_lolli.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_tyProd_inv A1 A2 B1 B2 s :
  TyProd A1 B1 s <: TyProd A2 B2 s -> A1 === A2 /\ B1 <: B2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/tyProd_inj[c1 [c2 _]]: TyProd A1 B1 s === TyProd A2 B2 s.
     exact: conv_trans c2.
    split=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> A C1 C2 s0 sb /tyProd_inj[c1 [c2 e1]] /tyProd_inj[c3 [c4 e2]]. 
    subst; split.
    exact: conv_trans c3. exact: SubI sb c2 c4.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_lnProd_inv A1 A2 B1 B2 s :
  LnProd A1 B1 s <: LnProd A2 B2 s -> A1 === A2 /\ B1 <: B2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/lnProd_inj[c1 [c2 _]]: LnProd A1 B1 s === LnProd A2 B2 s.
     exact: conv_trans c2.
    split=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> A C1 C2 s0 sb /lnProd_inj[c1 [c2 e1]] /lnProd_inj[c3 [c4 e2]]. 
    subst; split.
    exact: conv_trans c3. exact: SubI sb c2 c4.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_arrow_inv A1 A2 B1 B2 s :
  Arrow A1 B1 s <: Arrow A2 B2 s -> A1 === A2 /\ B1 <: B2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/arrow_inj[c1 [c2 _]]: Arrow A1 B1 s === Arrow A2 B2 s.
     exact: conv_trans c2.
    split=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> A C1 C2 s0 sb /arrow_inj[c1 [c2 e1]] /arrow_inj[c3 [c4 e2]]. 
    subst; split.
    exact: conv_trans c3. exact: SubI sb c2 c4.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_lolli_inv A1 A2 B1 B2 s :
  Lolli A1 B1 s <: Lolli A2 B2 s -> A1 === A2 /\ B1 <: B2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/lolli_inj[c1 [c2 _]]: Lolli A1 B1 s === Lolli A2 B2 s.
     exact: conv_trans c2.
    split=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> A C1 C2 s0 sb /lolli_inj[c1 [c2 e1]] /lolli_inj[c3 [c4 e2]]. 
    subst; split.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst sigma A B : sub1 A B -> sub1 A.[sigma] B.[sigma].
Proof. move=> s. elim: s sigma => /=; eauto using sub1. Qed.

Lemma sub_subst sigma A B : A <: B -> v_subst sigma -> A.[sigma] <: B.[sigma].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Lemma sub_ren A B xi : A <: B -> A.[ren xi] <: B.[ren xi].
Proof.
  intros.
  apply sub_subst; eauto.
  unfold v_subst.
  intros.
  constructor.
Qed.

Reserved Notation "[ Gamma |= ]".
Reserved Notation "[ Gamma |= m :- A -: s ]".
  
Inductive has_type : context term -> term -> term -> sort -> Prop :=
| axiom Gamma s l : 
  pure Gamma ->
  [ Gamma |= Sort s l :- Sort U l.+1 -: U ]
| u_prod Gamma A B s l :
  pure Gamma ->
  [ Gamma |= A :- Sort U l -: U ] ->
  [ A :L Gamma |= B :- Sort s l -: U ] ->
  [ Gamma |= TyProd A B s :- Sort U l -: U ]
| l_prod Gamma A B s l :
  pure Gamma ->
  [ Gamma |= A :- Sort U l -: U ] ->
  [ A :L Gamma |= B :- Sort s l -: U ] ->
  [ Gamma |= LnProd A B s :- Sort L l -: U ]
| arrow Gamma A B s l :
  pure Gamma ->
  [ Gamma |= A :- Sort L l -: U ] ->
  [ Gamma |= B :- Sort s l -: U ] ->
  [ Gamma |= Arrow A B s :- Sort U l -: U ]
| lolli Gamma A B s l :
  pure Gamma ->
  [ Gamma |= A :- Sort L l -: U ] ->
  [ Gamma |= B :- Sort s l -: U ] ->
  [ Gamma |= Lolli A B s :- Sort L l -: U ]
| u_var Gamma x A : 
  hasL Gamma x A ->
  [ Gamma |= Var x :- A -: U ]
| l_var Gamma x A :
  hasR Gamma x A ->
  [ Gamma |= Var x :- A -: L ]
| u_lam1 Gamma n A B s l :
  pure Gamma ->
  [ Gamma |= TyProd A B s :- Sort U l -: U ] ->
  [ A :L Gamma |= n :- B -: s ] ->
  [ Gamma |= Lam n :- TyProd A B s -: U ]
| u_lam2 Gamma n A B s l :
  pure Gamma ->
  [ Gamma |= Arrow A B s :- Sort U l -: U ] ->
  [ A :R Gamma |= n :- B.[ren (+1)] -: s ] ->
  [ Gamma |= Lam n :- Arrow A B s -: U ]
| l_lam1 Gamma n A B s l :
  [ re Gamma |= LnProd A B s :- Sort L l -: U ] ->
  [ A :L Gamma |= n :- B -: s ] ->
  [ Gamma |= Lam n :- LnProd A B s -: L ]
| l_lam2 Gamma n A B s l :
  [ re Gamma |= Lolli A B s :- Sort L l -: U ] ->
  [ A :R Gamma |= n :- B.[ren (+1)] -: s ] ->
  [ Gamma |= Lam n :- Lolli A B s -: L ]
| u_app1 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |= m :- TyProd A B s -: U ] ->
  [ Gamma2 |= n :- A -: U ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |= App m n :- App (Lam B) n -: s ]
| u_app2 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |= m :- Arrow A B s -: U ] ->
  [ Gamma2 |= n :- A -: L ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |= App m n :- B -: s ]
| l_app1 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |= m :- LnProd A B s -: L ] ->
  [ Gamma2 |= n :- A -: U ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |= App m n :- App (Lam B) n -: s ]
| l_app2 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |= m :- Lolli A B s -: L ] ->
  [ Gamma2 |= n :- A -: L ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |= App m n :- B -: s ]
| conversion Gamma A B m s l :
  A <: B ->
  [ re Gamma |= B :- Sort s l -: U ] ->
  [ Gamma |= m :- A -: s ] ->
  [ Gamma |= m :- B -: s ]
where "[ Gamma |= m :- A -: s ]" := (has_type Gamma m A s).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |= ]
| u_ok Gamma A l :
  [ Gamma |= ] ->
  [ re Gamma |= A :- Sort U l -: U ] ->
  [ A :L Gamma |= ]
| l_ok Gamma A l :
  [ Gamma |= ] ->
  [ re Gamma |= A :- Sort L l -: U ] ->
  [ A :R Gamma |= ]
| n_ok Gamma :
  [ Gamma |= ] ->
  [ :N Gamma |= ]
where "[ Gamma |= ]" := (context_ok Gamma).

Lemma re_ok Gamma :
  [ Gamma |= ] ->
  [ re Gamma |= ].
Proof with eauto using context_ok.
  intros.
  induction H...
  - simpl.
    eapply u_ok...
    rewrite <- re_re; eauto.
  - simpl.
    apply n_ok.
    assumption.
  - simpl.
    apply n_ok.
    assumption.
Qed.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil xi :
  agree_ren xi nil nil
| agree_ren_L Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m :L Gamma) (m.[ren xi] :L Gamma')
| agree_ren_R Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m :R Gamma) (m.[ren xi] :R Gamma')
| agree_ren_N Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (:N Gamma) (:N Gamma')
| agree_ren_wkL Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) (Gamma) (m :L Gamma')
| agree_ren_wkN Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) (Gamma) (:N Gamma').

Lemma agree_ren_refl Gamma :
  agree_ren id Gamma Gamma.
Proof.
  induction Gamma.
  - constructor.
  - destruct a. 
    replace (agree_ren id (Left t :: Gamma) (Left t :: Gamma))
      with (agree_ren (upren id) (t :L Gamma) (t.[ren id] :L Gamma))
      by autosubst.
    constructor; eauto.
    replace (agree_ren id (Right t :: Gamma) (Right t :: Gamma))
      with (agree_ren (upren id) (t :R Gamma) (t.[ren id] :R Gamma))
      by autosubst.
    constructor; eauto.
    replace (agree_ren id (Null _ :: Gamma) (Null _ :: Gamma))
      with (agree_ren (upren id) (:N Gamma) (:N Gamma))
      by autosubst.
    constructor; eauto.
Qed.

Lemma agree_ren_pure Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  pure Gamma ->
  pure Gamma'.
Proof.
  induction 1; simpl; intros; eauto.
  - inv H0; eauto.
    constructor; eauto.
  - inv H0.
  - inv H0; subst; eauto.
    constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma agree_ren_re_re Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren xi (re Gamma) (re Gamma').
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma agree_ren_hasL Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  forall x A,
    hasL Gamma x A ->
    hasL Gamma' (xi x) A.[ren xi].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    eapply agree_ren_pure; eauto.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H.
  - inv H; subst.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
Qed.

Lemma agree_ren_hasR Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  forall x A,
    hasR Gamma x A ->
    hasR Gamma' (xi x) A.[ren xi].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    eapply agree_ren_pure; eauto.
  - inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
Qed.

Lemma merge_agree_ren_inv Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  forall Gamma1 Gamma2,
    merge Gamma1 Gamma2 Gamma ->
    exists Gamma1' Gamma2',
      merge Gamma1' Gamma2' Gamma' /\
      agree_ren xi Gamma1 Gamma1' /\
      agree_ren xi Gamma2 Gamma2'.
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    exists nil.
    repeat constructor.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren xi] :L x).
    exists (m.[ren xi] :L x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren xi] :R x).
    exists (:N x0).
    repeat constructor; eauto.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (:N x).
    exists (m.[ren xi] :R x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (:N x).
    exists (:N x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (m :L x).
    exists (m :L x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (:N x).
    exists (:N x0).
    repeat constructor; eauto.
Qed.

Lemma rename_ok Gamma m A s :
  [ Gamma |= m :- A -: s ] ->
  forall Gamma' xi,
    agree_ren xi Gamma Gamma' ->
    [ Gamma' |= m.[ren xi] :- A.[ren xi] -: s ].
Proof.
  intros H.
  induction H; simpl; intros.
  - pose proof (agree_ren_pure H0 H).
    apply axiom; assumption.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply u_prod; eauto.
    replace (Sort s l) with ((Sort s l).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply l_prod; eauto.
    replace (Sort s l) with ((Sort s l).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply arrow; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply lolli; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply u_var.
    eapply agree_ren_hasL; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply l_var.
    eapply agree_ren_hasR; eauto.
  - eapply u_lam1.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    asimpl.
    apply IHhas_type2; eauto.
    constructor; eauto.
  - asimpl.
    eapply u_lam2.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    replace (B.[ren xi].[ren (+1)]) 
      with (B.[ren (+1)].[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - eapply l_lam1.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    asimpl.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    eapply l_lam2.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    replace (B.[ren xi].[ren (+1)]) 
      with (B.[ren (+1)].[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    eapply u_app1; eauto.
  - pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    eapply u_app2; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    eapply l_app1; eauto.
  - pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    eapply l_app2; eauto.
  - eapply conversion.
    apply sub_ren; eauto.
    apply IHhas_type1.
    apply agree_ren_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma hasL_ok Gamma :
  [ Gamma |= ] ->
  forall x A,
    hasL Gamma x A ->
    exists l, [ re Gamma |= A :- Sort U l -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    exists l.
    replace (Sort U l) with ((Sort U l).[ren (+1)]) by autosubst.
    eapply rename_ok.
    apply H0.
    apply agree_ren_wkL.
    rewrite <- pure_re; eauto.
    apply agree_ren_refl.
    specialize (IHcontext_ok _ _ H6).
    inv IHcontext_ok.
    exists x.
    replace (Sort U x) with ((Sort U x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkL.
    apply agree_ren_refl.
  - inv H1.
  - inv H0.
    specialize (IHcontext_ok _ _ H2).
    inv IHcontext_ok.
    exists x.
    replace (Sort U x) with ((Sort U x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma hasR_ok Gamma :
  [ Gamma |= ] ->
  forall x A,
    hasR Gamma x A ->
    exists l, [ re Gamma |= A :- Sort L l -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    specialize (IHcontext_ok _ _ H6).
    inv IHcontext_ok.
    exists x.
    replace (Sort L x) with ((Sort L x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkL.
    apply agree_ren_refl.
  - inv H1; simpl.
    exists l.
    replace (Sort L l) with ((Sort L l).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
  - inv H0; simpl.
    specialize (IHcontext_ok _ _ H2).
    inv IHcontext_ok.
    exists x.
    replace (Sort L x) with ((Sort L x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma value_sound Gamma m A :
  [ Gamma |= m :- A -: U ] -> value m -> pure Gamma.
Proof.
  intros H.
  dependent induction H; intros; eauto.
  - eapply hasL_pure; eauto.
  - inv H2.
  - inv H2.
  - inv H2.
  - inv H2.
Qed.

Lemma weakening_L Gamma m A s B :
  [ Gamma |= m :- A -: s ] ->
  [ B :L Gamma |= m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkL.
  apply agree_ren_refl.
Qed.

Lemma weakening_N Gamma m A s :
  [ Gamma |= m :- A -: s ] ->
  [ :N Gamma |= m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkN.
  apply agree_ren_refl.
Qed.

Lemma eweakening_L Gamma m m' A A' s B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |= m :- A -: s ] -> 
  [ B :L Gamma |= m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakening_L; eauto.
Qed.

Lemma eweakening_N Gamma m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |= m :- A -: s ] -> 
  [ :N Gamma |= m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakening_N; eauto.
Qed.

Reserved Notation "[ Delta |= sigma =| Gamma ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil sigma :
  v_subst sigma ->
  [ nil |= sigma =| nil ]
| agree_subst_L Delta sigma Gamma A :
  [ Delta |= sigma =| Gamma ] ->
  [ A.[sigma] :L Delta |= up sigma =| A :L Gamma ]
| agree_subst_R Delta sigma Gamma A :
  [ Delta |= sigma =| Gamma ] ->
  [ A.[sigma] :R Delta |= up sigma =| A :R Gamma ]
| agree_subst_N Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] ->
  [ :N Delta |= up sigma =| :N Gamma ]
| agree_subst_wkL Delta sigma Gamma n A :
  value n ->
  [ Delta |= sigma =| Gamma ] ->
  [ re Delta |= n :- A.[sigma] -: U ] ->
  [ Delta |= n .: sigma =| A :L Gamma ]
| agree_subst_wkR Delta1 Delta2 Delta sigma Gamma n A :
  value n ->
  merge Delta1 Delta2 Delta ->
  [ Delta1 |= sigma =| Gamma ] ->
  [ Delta2 |= n :- A.[sigma] -: L ] ->
  [ Delta |= n .: sigma =| A :R Gamma ]
| agree_subst_wkN Delta sigma Gamma n :
  value n ->
  [ Delta |= sigma =| Gamma ] ->
  [ Delta |= n .: sigma =| :N Gamma ]
| agree_subst_convL Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |= B.[ren (+1)].[sigma] :- Sort U l -: U ] ->
  [ Delta |= sigma =| A :L Gamma ] ->
  [ Delta |= sigma =| B :L Gamma ]
| agree_subst_convR Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |= B.[ren (+1)].[sigma] :- Sort L l -: U ] ->
  [ re Gamma |= B :- Sort L l -: U ] ->
  [ Delta |= sigma =| A :R Gamma ] ->
  [ Delta |= sigma =| B :R Gamma ]
where "[ Delta |= sigma =| Gamma ]" := (agree_subst Delta sigma Gamma).

Lemma agree_subst_v_subst Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] -> v_subst sigma.
Proof.
  induction 1; intros; eauto.
  - apply v_subst_up; eauto.
  - apply v_subst_up; eauto.
  - apply v_subst_up; eauto.
  - apply v_subst_cons; eauto.
  - apply v_subst_cons; eauto.
  - apply v_subst_cons; eauto.
Qed.

Lemma agree_subst_pure Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] -> pure Gamma -> pure Delta.
Proof.
  induction 1; intros; eauto.
  inv H0.
  constructor; eauto.
  inv H0.
  inv H0.
  constructor; eauto.
  inv H2; eauto.
  inv H3.
  inv H1; eauto.
  inv H2.
  apply IHagree_subst.
  constructor; eauto.
  inv H3.
Qed.

Lemma agree_subst_refl Gamma :
  [ Gamma |= ids =| Gamma ].
Proof.
  induction Gamma.
  - constructor.
    apply ids_v_subst.
  - destruct a.
    replace ([Left t :: Gamma |= ids =| Left t :: Gamma])
      with ([Left t.[ids] :: Gamma |= up ids =| Left t :: Gamma])
      by autosubst.
    apply agree_subst_L; eauto.
    replace ([Right t :: Gamma |= ids =| Right t :: Gamma])
      with ([Right t.[ids] :: Gamma |= up ids =| Right t :: Gamma])
      by autosubst.
    apply agree_subst_R; eauto.
    replace (ids) with (up ids) by autosubst.
    apply agree_subst_N; eauto.
Qed.

Lemma agree_subst_hasL Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] ->
  forall x A,
    hasL Gamma x A -> 
    [ Delta |= sigma x :- A.[sigma] -: U ].
Proof.
  induction 1; intros.
  - inv H0.
  - inv H0.
    + asimpl.
      apply u_var.
      replace (A.[sigma >> ren (+1)]) 
        with (A.[sigma].[ren (+1)]) by autosubst.
      constructor.
      eapply agree_subst_pure; eauto.
    + eapply eweakening_L; eauto.
      autosubst.
      autosubst.
  - inv H0.
  - inv H0.
    eapply eweakening_N; eauto.
    autosubst.
    autosubst.
  - inv H2; asimpl; eauto.
    pose proof (agree_subst_pure H0 H7).
    pose proof (pure_re H2).
    rewrite H3; eauto.
  - inv H3.
  - inv H1; asimpl; eauto.
  - inv H2.
    + assert (hasL (A :L Gamma) 0 A.[ren (+1)]).
      constructor; eauto.
      eapply conversion.
      eapply sub_subst.
      eapply sub_ren; eauto.
      eapply agree_subst_v_subst; eauto.
      apply H0.
      apply IHagree_subst; eauto.
    + eapply IHagree_subst.
      constructor; eauto.
  - inv H3.
Qed.

Lemma agree_subst_hasR Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] ->
  forall x A,
    hasR Gamma x A -> 
    [ Delta |= sigma x :- A.[sigma] -: L ].
Proof.
  induction 1; intros.
  - inv H0.
  - inv H0.
    eapply eweakening_L; eauto.
    autosubst.
    autosubst.
  - inv H0.
    asimpl.
    replace (A.[sigma >> ren (+1)]) 
      with (A.[sigma].[ren (+1)]) by autosubst.
    constructor.
    constructor.
    eapply agree_subst_pure; eauto.
  - inv H0.
    eapply eweakening_N; eauto.
    autosubst.
    autosubst.
  - inv H2; asimpl; eauto.
  - inv H3; asimpl.
    pose proof (agree_subst_pure H1 H8).
    pose proof (merge_pure1 H0 H3).
    rewrite H4; eauto.
  - inv H1; asimpl; eauto.
  - inv H2.
    apply IHagree_subst.
    constructor; eauto.
  - inv H3.
    assert (hasR (A :R Gamma) 0 A.[ren (+1)]).
    constructor; eauto.
    eapply conversion.
    apply sub_subst.
    apply sub_ren; eauto.
    eapply agree_subst_v_subst; eauto.
    apply H0.
    apply IHagree_subst; eauto.
Qed.

Lemma agree_subst_re_re Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] ->
  [ re Delta |= sigma =| re Gamma ].
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
    rewrite <- re_re; eauto.
  - constructor; eauto.
    pose proof (merge_re_re H0).
    destruct H3.
    rewrite <- H3; eauto.
  - constructor; eauto.
  - simpl in IHagree_subst.
    eapply agree_subst_convL.
    apply H.
    rewrite <- re_re.
    apply H0.
    apply IHagree_subst.
Qed.

Lemma merge_agree_subst_inv Delta sigma Gamma :
  [ Delta |= sigma =| Gamma ] ->
  forall Gamma1 Gamma2,
    merge Gamma1 Gamma2 Gamma ->
    exists Delta1 Delta2,
      merge Delta1 Delta2 Delta /\
      [ Delta1 |= sigma =| Gamma1 ] /\
      [ Delta2 |= sigma =| Gamma2 ].
Proof.
  intros H.
  dependent induction H; intros.
  - inv H0.
    exists nil.
    exists nil.
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (A.[sigma] :L x).
    exists (A.[sigma] :L x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (A.[sigma] :R x).
    exists (:N x0).
    repeat constructor; eauto.
  - pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (:N x).
    exists (A.[sigma] :R x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (:N x).
    exists (:N x0).
    repeat constructor; eauto.
  - inv H2.
    pose proof (IHagree_subst _ _ H6).
    first_order.
    exists x.
    exists x0.
    pose proof (merge_re_re H2).
    destruct H5.
    repeat constructor; eauto.
    rewrite H5; eauto.
    rewrite H7; eauto.
  - inv H3.
    + pose proof (IHagree_subst _ _ H7).
      firstorder.
      pose proof (merge_split1 H0 H3).
      firstorder.
      exists x1.
      exists x0.
      firstorder.
      eapply agree_subst_wkR.
      apply H.
      apply H6.
      apply H4.
      apply H2.
      eapply agree_subst_wkN; eauto.
    + pose proof (IHagree_subst _ _ H7).
      firstorder.
      pose proof (merge_split2 H0 H3).
      firstorder.
      exists x.
      exists x1.
      firstorder.
      apply agree_subst_wkN; eauto.
      eapply agree_subst_wkR.
      apply H.
      apply H6.
      apply H5.
      apply H2.
  - inv H1.
    pose proof (IHagree_subst _ _ H5).
    first_order.
    exists x.
    exists x0.
    repeat constructor; eauto.
  - inv H2.
    assert (merge (A :L Gamma0) (A :L Gamma3) (A :L Gamma)).
    apply merge_left; eauto.
    specialize (IHagree_subst _ _ H2).
    first_order.
    exists x.
    exists x0.
    pose proof (merge_re_re H3).
    inv H7.
    repeat constructor; eauto.
    eapply agree_subst_convL; eauto.
    rewrite H8; eauto.
    eapply agree_subst_convL; eauto.
    rewrite H9; eauto.
  - inv H3.
    + assert (merge (A :R Gamma0) (:N Gamma3) (A :R Gamma)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H3).
      first_order.
      exists x.
      exists x0.
      pose proof (merge_re_re H4). inv H8.
      pose proof (merge_re_re H7). inv H8.
      repeat constructor; eauto.
      eapply agree_subst_convR; eauto.
      rewrite H9; eauto.
      rewrite H11; eauto.
    + assert (merge (:N Gamma0) (A :R Gamma3) (A :R Gamma)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H3).
      first_order.
      exists x.
      exists x0.
      pose proof (merge_re_re H4). inv H8.
      pose proof (merge_re_re H7). inv H8.
      repeat constructor; eauto.
      eapply agree_subst_convR; eauto.
      rewrite H10; eauto.
      rewrite H12; eauto.
Qed.

Lemma substitution Gamma m A s :
  [ Gamma |= m :- A -: s ] ->
  forall Delta sigma,
    [ Delta |= sigma =| Gamma ] ->
    [ Delta |= m.[sigma] :- A.[sigma] -: s ].
Proof.
  intros H.
  dependent induction H; asimpl; intros; eauto.
  - apply axiom.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply u_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply l_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    specialize (IHhas_type2 _ _ H2). asimpl in IHhas_type2.
    apply arrow; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    specialize (IHhas_type2 _ _ H2). asimpl in IHhas_type2.
    apply lolli; eauto.
    eapply agree_subst_pure; eauto.
  - eapply agree_subst_hasL; eauto.
  - eapply agree_subst_hasR; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H2).
    specialize (IHhas_type2 _ _ H3).
    eapply u_lam1; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_R A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    eapply u_lam2; eauto.
    eapply agree_subst_pure; eauto.
    asimpl; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H1).
    specialize (IHhas_type2 _ _ H3).
    eapply l_lam1; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_R A H1).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    eapply l_lam2; eauto.
    asimpl; eauto.
  - pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    eapply u_app1; eauto.
  - pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    eapply u_app2; eauto.
  - pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    eapply l_app1; eauto.
  - pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    eapply l_app2; eauto.
  - eapply conversion.
    apply sub_subst; eauto.
    eapply agree_subst_v_subst; eauto.
    apply IHhas_type1; eauto.
    apply agree_subst_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma substitutionL Gamma1 m A B s :
  [ A :L Gamma1 |= m :- B -: s ] ->
  forall Gamma2 Gamma n,
    value n ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |= n :- A -: U ] -> 
    [ Gamma |= m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  pose proof (value_sound H2 H0).
  pose proof (merge_pure2 H1 H3).
  rewrite H4.
  apply agree_subst_wkL; eauto.
  apply agree_subst_refl.
  pose proof (merge_re_re H1).
  destruct H5.
  asimpl.
  rewrite H5.
  rewrite <- H6.
  rewrite <- pure_re; eauto.
Qed.

Lemma substitutionN Gamma1 m A B s :
  [ :N Gamma1 |= m :- B -: s ] ->
  forall Gamma2 n t,
    value n ->
    [ Gamma2 |= n :- A -: t ] -> 
    [ Gamma1 |= m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  apply agree_subst_wkN; eauto.
  apply agree_subst_refl.
Qed.

Lemma substitutionR Gamma1 m A B s :
  [ A :R Gamma1 |= m :- B -: s ] ->
  forall Gamma2 Gamma n,
    value n ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |= n :- A -: L ] -> 
    [ Gamma |= m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  eapply agree_subst_wkR; asimpl; eauto.
  apply agree_subst_refl.
Qed.

Lemma context_convL Gamma m A B C s l :
  B === A -> 
  [ re Gamma |= A :- Sort U l -: U ] ->
  [ A :L Gamma |= m :- C -: s ] -> 
  [ B :L Gamma |= m :- C -: s ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B :L Gamma |= m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp2.
  eapply agree_subst_convL; simpl.
  eapply conv_sub; eauto.
  pose proof (weakening_L B tp1).
  asimpl.
  asimpl in H.
  apply H.
  apply agree_subst_refl.
Qed.

Lemma context_convR Gamma m A B C s l :
  B === A -> 
  [ re Gamma |= A :- Sort L l -: U ] ->
  [ A :R Gamma |= m :- C -: s ] -> 
  [ B :R Gamma |= m :- C -: s ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B :R Gamma |= m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp2.
  eapply agree_subst_convR; simpl.
  eapply conv_sub; eauto.
  pose proof (weakening_N tp1).
  asimpl.
  asimpl in H.
  apply H.
  apply tp1.
  apply agree_subst_refl.
Qed.

Lemma tyProd_invX Gamma A B s srt :
  [ re Gamma |= TyProd A B s :- srt -: U ] -> 
  forall l, srt === Sort U l ->
    [ re Gamma |= A :- Sort U l -: U ] /\ 
    [ A :L re Gamma |= B :- Sort s l -: U ].
Proof.
  move e:(TyProd A B s) => n tp. 
  elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s l p tp1 _ tp2 _ A0 B0 s0 [->->->] l0 /sort_inj[_<-] => //.
  move=> Gamma A B m s l e1 tp1 ih1 tp2 ih2 A0 B0 s0 h l0 e2.
  eapply ih2; eauto.
  eapply conv_trans.
  apply e1.
  apply e2.
Qed.

Lemma tyProd_inv Gamma A B s l :
  [ re Gamma |= TyProd A B s :- Sort U l -: U ] -> 
  [ re Gamma |= A :- Sort U l -: U ] /\ 
  [ A :L re Gamma |= B :- Sort s l -: U ].
Proof.
  intros.
  eapply tyProd_invX; eauto.
Qed.

Lemma arrow_invX Gamma A B s srt :
  [ re Gamma |= Arrow A B s :- srt -: U ] ->
  forall l, srt === Sort U l ->
    [ re Gamma |= A :- Sort L l -: U ] /\ 
    [ re Gamma |= B :- Sort s l -: U ].
Proof.
  move e:(Arrow A B s) => n tp. 
  elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s l p tp1 _ tp2 _ A0 B0 s0 [->->->] l0 /sort_inj[_<-] => //.
  move=> Gamma A B m l s e1 tp1 ih1 tp2 ih2 A0 B0 s0 h l0 e2.
  eapply ih2; eauto.
  eapply conv_trans.
  apply e1.
  apply e2.
Qed.

Lemma arrow_inv Gamma A B s l :
  [ re Gamma |= Arrow A B s :- Sort U l -: U ] ->
  [ re Gamma |= A :- Sort L l -: U ] /\ 
  [ re Gamma |= B :- Sort s l -: U ].
Proof.
  intros.
  eapply arrow_invX; eauto.
Qed.

Lemma lnProd_invX Gamma A B s srt :
  [ re Gamma |= LnProd A B s :- srt -: U ] ->
  forall l, srt === Sort L l ->
    [ re Gamma |= A :- Sort U l -: U ] /\ 
    [ A :L re Gamma |= B :- Sort s l -: U ].
Proof.
  move e:(LnProd A B s) => n tp. 
  elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s l p tp1 _ tp2 _ A0 B0 s0 [->->->] l0 /sort_inj[_<-] => //.
  move=> Gamma A B m l s e1 tp1 ih1 tp2 ih2 A0 B0 s0 h l0 e2.
  eapply ih2; eauto.
  eapply conv_trans.
  apply e1.
  apply e2.
Qed.

Lemma lnProd_inv Gamma A B s l :
  [ re Gamma |= LnProd A B s :- Sort L l -: U ] ->
  [ re Gamma |= A :- Sort U l -: U ] /\ 
  [ A :L re Gamma |= B :- Sort s l -: U ].
Proof.
  intros.
  eapply lnProd_invX; eauto.
Qed.

Lemma lolli_invX Gamma A B s srt :
  [ re Gamma |= Lolli A B s :- srt -: U ] ->
  forall l, srt === Sort L l ->
    [ re Gamma |= A :- Sort L l -: U ] /\ 
    [ re Gamma |= B :- Sort s l -: U ].
Proof.
  move e:(Lolli A B s) => n tp. 
  elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s l p tp1 _ tp2 _ A0 B0 s0 [->->->] l0 /sort_inj[_<-] => //.
  move=> Gamma A B m l s e1 tp1 ih1 tp2 ih2 A0 B0 s0 h l0 e2.
  eapply ih2; eauto.
  eapply conv_trans.
  apply e1.
  apply e2.
Qed.

Lemma lolli_inv Gamma A B s l :
  [ re Gamma |= Lolli A B s :- Sort L l -: U ] ->
  [ re Gamma |= A :- Sort L l -: U ] /\ 
  [ re Gamma |= B :- Sort s l -: U ].
Proof.
  intros.
  eapply lolli_invX; eauto.
Qed.

Lemma u_lam1_invX Gamma n C :
  [ Gamma |= Lam n :- C -: U ] -> 
  forall A B s l, 
    (C === TyProd A B s /\ [A :L re Gamma |= B :- Sort s l -: U]) ->
    [ A :L Gamma |= n :- B -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  + apply tyProd_inj in H2.
    first_order; subst.
    eapply conversion.
    apply H4.
    apply H3. 
    eapply context_convL.
    apply conv_sym; apply H2.
    pose proof (pure_re H).
    rewrite H5 in H0.
    apply tyProd_inv in H0. inv H0.
    apply H6.
    apply H1.
  + solve_conv; exfalso; eauto.
  + eapply IHhas_type2; eauto.
    split.
    eapply conv_trans.
    apply H.
    apply H2.
    apply H3.
Qed.

Lemma u_lam1_inv Gamma n A B s l :
  [ re Gamma |= TyProd A B s :- Sort U l -: U ] ->
  [ Gamma |= Lam n :- TyProd A B s -: U ] -> 
  [ A :L Gamma |= n :- B -: s ].
Proof.
  intros.
  eapply u_lam1_invX; eauto.
  split.
  constructor.
  apply tyProd_inv in H; inv H.
  apply H2.
Qed.

Lemma u_lam2_invX Gamma n C :
  [ Gamma |= Lam n :- C -: U ] -> 
  forall A B s l, 
    (C === Arrow A B s /\ [re Gamma |= B :- Sort s l -: U]) ->
    [ A :R Gamma |= n :- B.[ren (+1)] -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  - solve_conv; exfalso; eauto.
  - apply arrow_inj in H2.
    first_order; subst.
    eapply conversion.
    apply conv_subst.
    apply ren_v_subst.
    apply H4.
    simpl.
    pose proof (weakening_N H3).
    apply H5.
    eapply context_convR.
    apply conv_sym; apply H2.
    pose proof (pure_re H).
    rewrite H5 in H0.
    apply arrow_inv in H0. inv H0.
    apply H6.
    apply H1.
  + eapply IHhas_type2; eauto.
    split.
    eapply conv_trans.
    apply H.
    apply H2.
    apply H3.
Qed.

Lemma u_lam2_inv Gamma n A B s l :
  [ re Gamma |= Arrow A B s :- Sort U l -: U ] ->
  [ Gamma |= Lam n :- Arrow A B s -: U ] -> 
  [ A :R Gamma |= n :- B.[ren (+1)] -: s ].
Proof.
  intros.
  eapply u_lam2_invX; eauto.
  split.
  constructor.
  apply arrow_inv in H; inv H.
  apply H2.
Qed.

Lemma l_lam1_invX Gamma n C :
  [ Gamma |= Lam n :- C -: L ] -> 
  forall A B s l, 
    (C === LnProd A B s /\ [A :L re Gamma |= B :- Sort s l -: U]) ->
    [ A :L Gamma |= n :- B -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  + apply lnProd_inj in H1.
    first_order; subst.
    eapply conversion.
    apply H3.
    apply H2. 
    eapply context_convL.
    apply conv_sym; apply H1.
    apply lnProd_inv in H. inv H.
    apply H4.
    apply H0.
  + solve_conv; exfalso; eauto.
  + eapply IHhas_type2; eauto.
    split.
    eapply conv_trans.
    apply H.
    apply H2.
    apply H3.
Qed.

Lemma l_lam1_inv Gamma n A B s l :
  [ re Gamma |= LnProd A B s :- Sort L l -: U ] ->
  [ Gamma |= Lam n :- LnProd A B s -: L ] -> 
  [ A :L Gamma |= n :- B -: s ].
Proof.
  intros.
  eapply l_lam1_invX; eauto.
  split.
  constructor.
  apply lnProd_inv in H; inv H.
  apply H2.
Qed.

Lemma l_lam2_invX Gamma n C :
  [ Gamma |= Lam n :- C -: L ] -> 
  forall A B s l, 
    (C === Lolli A B s /\ [re Gamma |= B :- Sort s l -: U]) ->
    [ A :R Gamma |= n :- B.[ren (+1)] -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  - solve_conv; exfalso; eauto.
  - apply lolli_inj in H1.
    first_order; subst.
    eapply conversion.
    apply conv_subst.
    apply ren_v_subst.
    apply H3.
    simpl.
    pose proof (weakening_N H2).
    apply H4.
    eapply context_convR.
    apply conv_sym; apply H1.
    apply lolli_inv in H. inv H.
    apply H4.
    apply H0.
  + eapply IHhas_type2; eauto.
    split.
    eapply conv_trans.
    apply H.
    apply H2.
    apply H3.
Qed.

Lemma l_lam2_inv Gamma n A B s l :
  [ re Gamma |= Lolli A B s :- Sort L l -: U ] ->
  [ Gamma |= Lam n :- Lolli A B s -: L ] -> 
  [ A :R Gamma |= n :- B.[ren (+1)] -: s ].
Proof.
  intros.
  eapply l_lam2_invX; eauto.
  split.
  constructor.
  apply lolli_inv in H; inv H.
  apply H2.
Qed.

Lemma merge_context_ok_inv Gamma Gamma1 Gamma2 :
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |= ] ->
  [ Gamma1 |= ] /\ [ Gamma2 |= ].
Proof.
  induction 1; intros.
  - repeat constructor.
  - inv H0.
    apply IHmerge in H3.
    apply merge_re_re in H. inv H.
    inv H3. split.
    eapply u_ok; eauto.
    rewrite H0; eauto.
    eapply u_ok; eauto.
    rewrite H1; eauto.
  - inv H0.
    apply IHmerge in H3.
    apply merge_re_re in H. inv H.
    inv H3; split.
    eapply l_ok; eauto.
    rewrite H0; eauto.
    constructor; eauto.
  - inv H0.
    apply IHmerge in H3.
    apply merge_re_re in H. inv H.
    inv H3; split.
    constructor; eauto.
    eapply l_ok; eauto.
    rewrite H1; eauto.
  - inv H0.
    apply IHmerge in H2.
    apply merge_re_re in H. inv H.
    inv H2; split; constructor; eauto.
Qed.

Theorem propagation Gamma m A s : 
  [ Gamma |= ] ->
  [ Gamma |= m :- A -: s ] ->
  exists l, [ re Gamma |= A :- Sort s l -: U ].
Proof.
  intros.
  dependent induction H0.
  - exists (l.+2).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - eapply hasL_ok; eauto.
  - eapply hasR_ok; eauto.
  - exists l.
    rewrite <- pure_re; eauto.
  - exists l.
    rewrite <- pure_re; eauto.
  - exists l; eauto.
  - exists l; eauto.
  - pose proof (merge_re_re H0). inv H1.
    apply merge_context_ok_inv in H0; eauto.
    inv H0.
    apply IHhas_type1 in H1. inv H1.
    apply tyProd_inv in H0. inv H0.
    exists x.
    pose proof (re_pure Gamma1).
    pose proof (u_prod H0 H1 H5).
    assert ([re Gamma1 |= TyProd A (Sort s x) U :- Sort U (x.+1) -: U ]).
    constructor; eauto.
    pose proof (u_lam1).
    eapply u_app2.


  
Qed.


Theorem preservation Gamma m A s :
  [ Gamma |= m :- A -: s ] ->
  forall n, pstep m n -> 
    [ Gamma |= n :- A -: s ].
Proof.
  intros.
  dependent induction H.
  - inv H0.
    apply axiom; eauto.
  - inv H2.
    specialize (IHhas_type1 _ H7).
    specialize (IHhas_type2 _ H8).
    apply u_prod; eauto.
    eapply context_convL.
    eapply conv1i; eauto.
    rewrite <- pure_re; eauto.
    apply IHhas_type2.
  - inv H2.
    specialize (IHhas_type1 _ H7).
    specialize (IHhas_type2 _ H8).
    apply l_prod; eauto.
    eapply context_convL.
    eapply conv1i; eauto.
    rewrite <- pure_re; eauto.
    apply IHhas_type2.
  - inv H2.
    specialize (IHhas_type1 _ H7).
    specialize (IHhas_type2 _ H8).
    apply arrow; eauto.
  - inv H2.
    specialize (IHhas_type1 _ H7).
    specialize (IHhas_type2 _ H8).
    apply lolli; eauto.
  - inv H0.
    apply u_var; eauto.
  - inv H0.
    apply l_var; eauto.
  - inv H2.
    specialize (IHhas_type2 _ H4).
    eapply u_lam1; eauto.
  - inv H2.
    specialize (IHhas_type2 _ H4).
    eapply u_lam2; eauto.
  - inv H1.
    specialize (IHhas_type2 _ H3).
    eapply l_lam1; eauto.
  - inv H1.
    specialize (IHhas_type2 _ H3).
    eapply l_lam2; eauto.
  - inv H2.
    + specialize (IHhas_type1 _ H5).
      specialize (IHhas_type2 _ H7).
      assert (pstep (App (Lam B) n) (App (Lam B) n')).
      constructor; eauto.
      apply pstep_refl.
      eapply conversion.
      apply conv1i; eauto.
      eapply u_app1; eauto.
    + assert (pstep (Lam n1) (Lam n')).
      constructor; eauto.
      specialize (IHhas_type1 _ H2).
      specialize (IHhas_type2 _ H8).
      eapply u_lam1_inv in IHhas_type1; eauto.
      assert (pstep (App (Lam B) n) (B.[v'/])).
      constructor; eauto.
      apply pstep_refl.
      eapply conversion.
      apply conv1i; eauto.
      eapply substitutionL.
      apply IHhas_type1.
      eapply pstep_value; eauto.
      apply H1.
      apply IHhas_type2.
  - inv H2.
    + specialize (IHhas_type1 _ H5).
      specialize (IHhas_type2 _ H7).
      eapply u_app2; eauto.
    + assert (pstep (Lam n1) (Lam n')).
      constructor; eauto.
      specialize (IHhas_type1 _ H2).
      specialize (IHhas_type2 _ H8).
      eapply u_lam2_inv in IHhas_type1; eauto.
      replace B with (B.[ren (+1)].[v'/]) by autosubst.
      eapply substitutionR.
      apply IHhas_type1.
      eapply pstep_value; eauto.
      apply H1.
      apply IHhas_type2.
  - inv H2.
    + specialize (IHhas_type1 _ H5).
      specialize (IHhas_type2 _ H7).
      assert (pstep (App (Lam B) n) (App (Lam B) n')).
      constructor; eauto.
      apply pstep_refl.
      eapply conversion.
      apply conv1i; eauto.
      eapply l_app1; eauto.
    + assert (pstep (Lam n1) (Lam n')).
      constructor; eauto.
      specialize (IHhas_type1 _ H2).
      specialize (IHhas_type2 _ H8).
      eapply l_lam1_inv in IHhas_type1; eauto.
      assert (pstep (App (Lam B) n) (B.[v'/])).
      constructor; eauto.
      apply pstep_refl.
      eapply conversion.
      apply conv1i; eauto.
      eapply substitutionL.
      apply IHhas_type1.
      eapply pstep_value; eauto.
      apply H1.
      apply IHhas_type2.
  - inv H2.
    + specialize (IHhas_type1 _ H5).
      specialize (IHhas_type2 _ H7).
      eapply l_app2; eauto.
    + assert (pstep (Lam n1) (Lam n')).
      constructor; eauto.
      specialize (IHhas_type1 _ H2).
      specialize (IHhas_type2 _ H8).
      eapply l_lam2_inv in IHhas_type1; eauto.
      replace B with (B.[ren (+1)].[v'/]) by autosubst.
      eapply substitutionR.
      apply IHhas_type1.
      eapply pstep_value; eauto.
      apply H1.
      apply IHhas_type2.
  - eapply conversion; eauto.
Qed.

Corollary preservation_step m n :
  step m n ->
  forall Gamma A s,
    [ Gamma |= m :- A -: s ] ->
    [ Gamma |= n :- A -: s ].
Proof.
  intros.
  eapply preservation.
  apply H0.
  apply step_pstep; eauto.
Qed.

Corollary preservation_star_step m n :
  star step m n ->
  forall Gamma A s,
    [ Gamma |= m :- A -: s ] ->
    [ Gamma |= n :- A -: s ].
Proof.
  intro H.
  dependent induction H; intros; eauto.
  eapply preservation.
  apply IHstar; eauto.
  apply step_pstep; eauto.
Qed.

Lemma canonical_tyProd m C :
  [ nil |= m :- C -: U ] -> value m ->
  forall A B s, 
    C === TyProd A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - inv H.
  - exists n; eauto.
  - solve_conv; exfalso; eauto.
  - inv H2.
  - inv H2.
  - inv H2.
  - inv H2.
  - eapply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H2.
Qed.

Lemma canonical_lnProd m C :
  [ nil |= m :- C -: L ] -> value m ->
  forall A B s, 
    C === LnProd A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - inv H.
  - exists n; eauto.
  - solve_conv; exfalso; eauto.
  - inv H2.
  - inv H2.
  - inv H2.
  - inv H2.
  - eapply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H2.
Qed.


Lemma canonical_arrow m C :
  [ nil |= m :- C -: U ] -> value m ->
  forall A B s, 
    C === Arrow A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - solve_conv; exfalso; eauto.
  - inv H.
  - solve_conv; exfalso; eauto.
  - exists n; eauto.
  - inv H2.
  - inv H2.
  - inv H2.
  - inv H2.
  - eapply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H2.
Qed.

Lemma canonical_lolli m C :
  [ nil |= m :- C -: L ] -> value m ->
  forall A B s, 
    C === Lolli A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - inv H.
  - solve_conv; exfalso; eauto.
  - exists n; eauto.
  - inv H2.
  - inv H2.
  - inv H2.
  - inv H2.
  - eapply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H2.
Qed.

Theorem progress m A s :
  [ nil |= m :- A -: s ] -> value m \/ exists n, step m n.
Proof.
  intros.
  dependent induction H.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - inv H.
  - inv H.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - right.
    inv H1.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H1).
    specialize (IHhas_type2 H1).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_tyProd; eauto.
      destruct H4; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H3.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
  - right.
    inv H1.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H1).
    specialize (IHhas_type2 H1).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_arrow; eauto.
      destruct H4; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H3.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
  - right.
    inv H1.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H1).
    specialize (IHhas_type2 H1).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_lnProd; eauto.
      destruct H4; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H3.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
  - right.
    inv H1.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H1).
    specialize (IHhas_type2 H1).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_lolli; eauto.
      destruct H4; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H3.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
  - apply IHhas_type; eauto.
Qed.

Import CoC.

Fixpoint erase (m : DLTT.term) : CoC.term :=
  match m with
  | DLTT.Var x => CoC.Var x
  | DLTT.Sort _ l => CoC.Sort l
  | DLTT.TyProd A B _ => CoC.Prod (erase A) (erase B)
  | DLTT.LnProd A B _ => CoC.Prod (erase A) (erase B)
  | DLTT.Arrow A B _ => CoC.Prod (erase A) (erase B).[ren (+1)]
  | DLTT.Lolli A B _ => CoC.Prod (erase A) (erase B).[ren (+1)]
  | DLTT.Lam n => CoC.Lam (erase n)
  | DLTT.App m n => CoC.App (erase m) (erase n)
  end.

Fixpoint erase_context 
  (Gamma : DLTT.context DLTT.term) 
: CoC.context CoC.term :=
  match Gamma with
  | Left t :: Gamma => erase t :s erase_context Gamma
  | Right t :: Gamma => erase t :s erase_context Gamma
  | Null :: Gamma => :n erase_context Gamma
  | nil => nil
  end.

Notation "[| m |]" := (erase m).
Notation "[[ Gamma ]]" := (erase_context Gamma).

Lemma erase_value v : 
  DLTT.value v <-> CoC.value [|v|].
Proof.
  split.
  induction 1; simpl; constructor.
  induction v; simpl; try constructor.
  intros.
  inv H.
Qed.

Definition erase_subst 
  (sigma : var -> DLTT.term) 
  (tau : var -> CoC.term)
: Prop := 
  forall x, [|sigma x|] = tau x.

Lemma erase_ren_com m :
  forall xi, [| m |].[ren xi] = [| m.[ren xi] |].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm1. 
    replace ([|m2|].[ren (xi >>> (+1))])
      with ([|m2|].[ren xi].[ren (+1)]) by autosubst.
    rewrite IHm2; eauto.
  - rewrite IHm1. 
    replace ([|m2|].[ren (xi >>> (+1))])
      with ([|m2|].[ren xi].[ren (+1)]) by autosubst.
    rewrite IHm2; eauto.
  - rewrite IHm; eauto.
  - rewrite IHm1 IHm2; eauto.
Qed.

Lemma erase_subst_up sigma tau :
  erase_subst sigma tau -> erase_subst (up sigma) (up tau).
Proof.
  unfold erase_subst.
  intros.
  induction x; asimpl; eauto.
  rewrite <-H.
  rewrite erase_ren_com; eauto.
Qed.

Lemma erase_subst_com m :
  forall sigma tau, 
    erase_subst sigma tau ->
    [| m.[sigma] |] = [| m |].[tau].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite <- (IHm sigma); eauto.
    rewrite <- (IHm0 (up sigma)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm sigma); eauto.
    rewrite <- (IHm0 (up sigma)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm1 sigma); eauto.
    rewrite (IHm2 _ tau); autosubst.
  - rewrite <- (IHm1 sigma); eauto.
    rewrite (IHm2 _ tau); autosubst.
  - rewrite <- (IHm (up sigma)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm1 sigma); eauto.
    rewrite <- (IHm2 sigma); eauto.
Qed.

Lemma erase_pstep m n :
  DLTT.pstep m n -> CoC.pstep [|m|] [|n|].
Proof with eauto using pstep, pstep_refl.
  induction 1; simpl; intros...
  erewrite erase_subst_com.
  eapply pstep_beta; eauto.
  unfold erase_subst; intros; destruct x; asimpl; eauto.
  constructor; eauto.
  apply pstep_ren; eauto.
  constructor; eauto.
  apply pstep_ren; eauto.
Qed.

Lemma erase_conv m n :
  conv DLTT.pstep m n -> conv CoC.pstep [|m|] [|n|].
Proof.
  induction 1; eauto.
  eapply conv_trans.
  apply IHconv.
  eapply convSE; eauto.
  apply erase_pstep; eauto.
  eapply convSEi; eauto.
  apply erase_pstep; eauto.
Qed.

Lemma hasL_erase Gamma x A :
  hasL Gamma x A -> has [[ Gamma ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Lemma hasR_erase Gamma x A :
  hasR Gamma x A -> has [[ Gamma ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Inductive agree_wk : 
  CoC.context CoC.term -> CoC.context CoC.term -> Prop :=
| agree_wk_nil : agree_wk nil nil
| agree_wk_s Gamma1 Gamma2 e :
  agree_wk Gamma1 Gamma2 ->
  agree_wk (e :: Gamma1) (e :: Gamma2)
| agree_wk_n Gamma1 Gamma2 A :
  agree_wk Gamma1 Gamma2 ->
  agree_wk (:n Gamma1) (A :s Gamma2).

Lemma agree_wk_has Gamma1 Gamma2 :
  agree_wk Gamma1 Gamma2 ->
  forall x A,
    has Gamma1 x A ->
    has Gamma2 x A.
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  inv H0; constructor; eauto.
  inv H0; constructor; eauto.
Qed.

Lemma agree_wk_re Gamma :
  agree_wk [[re Gamma]] [[Gamma]].
Proof.
  induction Gamma.
  - simpl; constructor.
  - destruct a; simpl; constructor; eauto.
Qed.

Lemma agree_wk_merge_inv Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  agree_wk [[Gamma1]] [[Gamma]] /\
  agree_wk [[Gamma2]] [[Gamma]].
Proof with eauto using agree_wk.
  intro H.
  dependent induction H; simpl; firstorder...
Qed.

Lemma wk_ok Gamma1 m A : 
  [ Gamma1 |- m :- A ] ->
  forall Gamma2, agree_wk Gamma1 Gamma2 ->
    [ Gamma2 |- m :- A ].
Proof.
  intro H.
  dependent induction H; simpl; intros; subst.
  - pose proof (agree_wk_has H0 H).
    apply ty_var; eauto.
  - apply ty_sort.
  - apply ty_prod.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_lam.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_app.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
  - eapply ty_conv.
    apply H.
    apply IHhas_type; eauto.
Qed.

Lemma erase_re Gamma m A :
  [ [[re Gamma]] |- m :- A ] ->
  [ [[Gamma]] |- m :- A ].
Proof.
  intro H.
  eapply wk_ok; eauto.
  apply agree_wk_re.
Qed.

Lemma erase_ok Gamma m A s : 
  [ Gamma |= m :- A -: s ] ->
  [ [[ Gamma ]] |- [| m |] :- [| A |] ].
Proof.
  intro H.
  dependent induction H; asimpl.
  - apply ty_sort.  
  - apply ty_prod.
    apply IHhas_type1.
    apply IHhas_type2.
  - apply ty_prod.
    apply IHhas_type1.
    apply IHhas_type2.
  - apply ty_prod.
    apply IHhas_type1.
    replace (Sort l) with ((Sort l).[ren (+1)]) by autosubst.
    apply weakening.
    apply IHhas_type2.
  - apply ty_prod.
    apply IHhas_type1.
    replace (Sort l) with ((Sort l).[ren (+1)]) by autosubst.
    apply weakening.
    apply IHhas_type2.
  - apply hasL_erase in H.
    apply ty_var; eauto.
  - apply hasR_erase in H.
    apply ty_var; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
    rewrite erase_ren_com; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
    apply erase_re; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
    apply erase_re; eauto.
    rewrite erase_ren_com; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[[|n|]/] === App (Lam [|B|]) [|n|]).
    eapply convSEi; eauto.
    econstructor; eauto using pstep_refl.
    eapply ty_conv.
    apply H2.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[ren (+1)].[[|n|]/] = [|B|]) by autosubst.
    eapply ty_conv.
    rewrite <- H2; eauto.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[[|n|]/] === App (Lam [|B|]) [|n|]).
    eapply convSEi; eauto.
    econstructor; eauto using pstep_refl.
    eapply ty_conv.
    apply H2.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[ren (+1)].[[|n|]/] = [|B|]) by autosubst.
    eapply ty_conv.
    rewrite <- H2; eauto.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - eapply ty_conv.
    apply erase_conv; eauto.
    apply IHhas_type.
Qed.

Lemma erase_context_ok Gamma :
  [ Gamma |= ] -> [ [[Gamma]] |- ].
Proof.
  induction 1; simpl. 
  constructor.
  apply erase_ok in H0.
  apply erase_re in H0.
  econstructor; eauto.
  apply erase_ok in H0.
  apply erase_re in H0.
  econstructor; eauto.
  constructor; eauto.
Qed.

Lemma erase_lam_inv m n :
  Lam n = [|m|] -> exists m', m = DLTT.Lam m'.
Proof.
  induction m; intros; try discriminate.
  simpl in H.
  inv H.
  exists n0; eauto.
Qed.

Lemma erase_pstep_cbv_inv m m1 :
  pstep_cbv [|m|] m1 ->
    exists m2, DLTT.pstep m m2 /\ m1 = [|m2|].
Proof with eauto using DLTT.pstep, CoC.pstep.
  intros.
  dependent induction H. 
  - destruct m; try discriminate; simpl. inv x. 
    exists (DLTT.Var x1)...
  - destruct m; try discriminate; simpl. inv x. 
    exists (DLTT.Sort srt l)...
  - destruct m; try discriminate; simpl. inv x. 
    assert ([|n|] = [|n|]) by eauto.
    apply IHpstep_cbv in H0.
    first_order; subst.
    exists (DLTT.Lam x)...
  - destruct m; try discriminate; simpl. inv x.
    destruct m1; try discriminate; simpl. inv H3.
    assert ([|n|] = [|n|]) by eauto.
    assert ([|m2|] = [|m2|]) by eauto.
    apply IHpstep_cbv1 in H2.
    apply IHpstep_cbv2 in H3.
    first_order; subst.
    exists (x0.[x/]). split.
    rewrite <- erase_value in H0.
    constructor; eauto.
    erewrite erase_subst_com; eauto.
    unfold erase_subst; intros; destruct x1; asimpl; eauto.
  - destruct m; try discriminate; simpl. inv x.
    assert ([|m1|] = [|m1|]) by eauto.
    assert ([|m2|] = [|m2|]) by eauto.
    apply IHpstep_cbv1 in H1.
    apply IHpstep_cbv2 in H2.
    first_order; subst.
    exists (DLTT.App x0 x)...
  - destruct m; try discriminate; simpl; inv x.
    + assert ([|m|] = [|m|]) by eauto.
      assert ([|B|] = [|B|]) by eauto.
      apply IHpstep_cbv1 in H1.
      apply IHpstep_cbv2 in H2.
      first_order; subst.
      exists (TyProd x0 x s)...
    + assert ([|m|] = [|m|]) by eauto.
      assert ([|B|] = [|B|]) by eauto.
      apply IHpstep_cbv1 in H1.
      apply IHpstep_cbv2 in H2.
      first_order; subst.
      exists (LnProd x0 x s)...
    + assert ([|m1|] = [|m1|]) by eauto.
      assert ([|m2|].[ren (+1)] = [|m2.[ren (+1)]|]).
      apply erase_ren_com.
      apply IHpstep_cbv1 in H1.
      apply IHpstep_cbv2 in H2.
      first_order; subst.
      apply pstep_ren1_inv in H2.
      first_order; subst.
      exists (Arrow x0 x1 s). split.
      constructor; eauto. 
      simpl; rewrite erase_ren_com; eauto.
    + assert ([|m1|] = [|m1|]) by eauto.
      assert ([|m2|].[ren (+1)] = [|m2.[ren (+1)]|]).
      apply erase_ren_com.
      apply IHpstep_cbv1 in H1.
      apply IHpstep_cbv2 in H2.
      first_order; subst.
      apply pstep_ren1_inv in H2.
      first_order; subst.
      exists (Lolli x0 x1 s). split.
      constructor; eauto. 
      simpl; rewrite erase_ren_com; eauto.
Qed.

Lemma erase_red_cbv_inv m m1 :
  red_cbv [|m|] m1 ->
    exists m2, DLTT.red m m2 /\ m1 = [|m2|].
Proof.
  intros.
  dependent induction H. 
  - exists m; eauto.
  - first_order; subst.
    pose proof (erase_pstep_cbv_inv H0).
    first_order; subst.
    exists x0; firstorder.
    eapply star_trans.
    apply H1.
    econstructor; eauto.
Qed.

Theorem strong_norm Gamma m A s :
  [ Gamma |= ] ->
  [ Gamma |= m :- A -: s ] ->
  exists v, DLTT.value v /\ DLTT.red m v.
Proof.
  intros.
  apply erase_context_ok in H.
  apply erase_ok in H0.
  pose proof (CoC.strong_cbv_norm H H0).
  first_order.
  apply erase_red_cbv_inv in H2.
  first_order; subst.
  exists x0. firstorder.
  rewrite erase_value; eauto.
Qed.

End DLTT.