From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sort : Type := U | L.

Definition elem T := option (T * sort).

Definition context T := seq (elem T).
Definition cons_u T (n : T) (Gamma : context T) : context T := 
  Some (n, U) :: Gamma.
Definition cons_l T (n : T) (Gamma : context T) : context T := 
  Some (n, L) :: Gamma.
Definition cons_s T (n : T) (s : sort) (Gamma : context T) : context T := 
  Some (n, s) :: Gamma.
Definition cons_n T (Gamma : context T) : context T := 
  None :: Gamma.

Notation "m :u Gamma" := (cons_u m Gamma) (at level 30).
Notation "m :l Gamma" := (cons_l m Gamma) (at level 30).
Notation "m :[ s ] Gamma" := (cons_s m s Gamma) (at level 30).
Notation ":n Gamma" := (cons_n Gamma) (at level 30).

Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  merge nil nil nil
| merge_left Gamma1 Gamma2 Gamma m : 
  merge Gamma1 Gamma2 Gamma ->
  merge (m :u Gamma1) (m :u Gamma2) (m :u Gamma)
| merge_right1 Gamma1 Gamma2 Gamma m :
  merge Gamma1 Gamma2 Gamma ->
  merge (m :l Gamma1) (:n Gamma2) (m :l Gamma)
| merge_right2 Gamma1 Gamma2 Gamma m :
  merge Gamma1 Gamma2 Gamma ->
  merge (:n Gamma1) (m :l Gamma2) (m :l Gamma)
| merge_null Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  merge (:n Gamma1) (:n Gamma2) (:n Gamma).

Inductive pure T : context T -> Prop :=
| pure_nil :
  pure nil
| pure_u Gamma m : 
  pure Gamma ->
  pure (m :u Gamma)
| pure_n Gamma : 
  pure Gamma ->
  pure (:n Gamma).

Inductive hasU {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| hasU_O m Gamma :
  pure Gamma ->
  hasU (m :u Gamma) 0 m.[ren (+1)]
| hasU_S Gamma v m n : 
  hasU Gamma v m ->
  hasU (n :u Gamma) (v.+1) m.[ren (+1)]
| hasU_N Gamma v m : 
  hasU Gamma v m ->
  hasU (:n Gamma) (v.+1) m.[ren (+1)].

Inductive hasL {T} `{Ids T} `{Subst T} :
  context T -> var -> T -> Prop :=
| hasL_O m Gamma :
  pure Gamma ->
  hasL (m :l Gamma) 0 m.[ren (+1)]
| hasL_S Gamma v m n :
  hasL Gamma v m ->
  hasL (n :u Gamma) (v.+1) m.[ren (+1)]
| hasL_N Gamma v m :
  hasL Gamma v m ->
  hasL (:n Gamma) (v.+1) m.[ren (+1)].

Fixpoint re T (Gamma : context T) : context T :=
  match Gamma with
  | Some (m, U) :: Gamma => Some (m, U) :: re Gamma
  | _ :: Gamma => None :: re Gamma
  | _ => nil
  end.

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
    case p; intros; simpl.
    case s; intros; simpl.
    rewrite <- IHGamma; eauto.
    rewrite <- IHGamma; eauto.
    rewrite <- IHGamma; eauto.
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
  destruct a; simpl. 
  destruct p; simpl. 
  destruct s; simpl. 
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> hasU (re Gamma) x A.
Proof.
  induction 1; simpl.
  - constructor.
    rewrite <- pure_re; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Gamma : context T) :
  forall x A, ~hasL (re Gamma) x A.
Proof.
  induction Gamma; unfold not; intros.
  - simpl in H1. inv H1.
  - destruct a; inv H1. 
    destruct p; inv H2. 
    destruct s; inv H4. 
    destruct p; inv H2. 
    destruct s; inv H4. 
    eapply IHGamma; eauto.
    destruct p; inv H2. 
    destruct s; inv H4. 
    eapply IHGamma; eauto.
    eapply IHGamma; eauto.
Qed.

Lemma hasU_pure {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> pure Gamma.
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma hasU_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A ->
  forall B,
    hasU Gamma x B ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasU in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasU in H5. rewrite H5; eauto.
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

Lemma hasU_hasL {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A ->
  forall B,
    ~ hasL Gamma x B.
Proof.
  induction 1; unfold not; intros.
  inv H2.
  inv H2; apply IHhasU in H7; eauto.
  inv H2; apply IHhasU in H5; eauto.
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
    exists (m :u x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m :l x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (:n x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m :l x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (:n x).
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
    exists (m :u x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (:n x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m :l x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m :l x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (:n x).
    repeat constructor; eauto.
Qed.

Inductive term : Type :=
| Var    (x : var)
| Sort   (s : sort)
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
| value_sort s       : value (Sort s)
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
| pstep_sort s :
  pstep (Sort s) (Sort s)
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
  - inv H0. exists (Sort s)...
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

Lemma conv_subst sigma s t : 
  v_subst sigma ->
  s === t -> s.[sigma] === t.[sigma].
Proof. 
  intro H.
  apply conv_hom. 
  intros.
  apply pstep_subst; eauto.
Qed.

Lemma rename_v_subst xi :
  v_subst (ren xi).
Proof.
  unfold v_subst.
  intros.
  constructor.
Qed.

Lemma rename_subst xi s t :
  s === t -> s.[ren xi] === t.[ren xi].
Proof.
  apply conv_subst.
  apply rename_v_subst.
Qed.

Lemma sort_ren_inv s v xi :
  Sort s = v.[ren xi] -> v = Sort s.
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

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- m :- A -: s ]".

Inductive has_type : context term -> term -> term -> sort -> Prop :=
| axiom Gamma s : 
  pure Gamma ->
  [ Gamma |- Sort s :- Sort U -: U ]
| u_prod Gamma A B s :
  pure Gamma ->
  [ Gamma |- A :- Sort U -: U ] ->
  [ A :u Gamma |- B :- Sort s -: U ] ->
  [ Gamma |- TyProd A B s :- Sort U -: U ]
| l_prod Gamma A B s :
  pure Gamma ->
  [ Gamma |- A :- Sort U -: U ] ->
  [ A :u Gamma |- B :- Sort s -: U ] ->
  [ Gamma |- LnProd A B s :- Sort L -: U ]
| arrow Gamma A B s :
  pure Gamma ->
  [ Gamma |- A :- Sort L -: U ] ->
  [ Gamma |- B :- Sort s -: U ] ->
  [ Gamma |- Arrow A B s :- Sort U -: U ]
| lolli Gamma A B s :
  pure Gamma ->
  [ Gamma |- A :- Sort L -: U ] ->
  [ Gamma |- B :- Sort s -: U ] ->
  [ Gamma |- Lolli A B s :- Sort L -: U ]
| u_var Gamma x A : 
  hasU Gamma x A ->
  [ Gamma |- Var x :- A -: U ]
| l_var Gamma x A :
  hasL Gamma x A ->
  [ Gamma |- Var x :- A -: L ]
| u_lam1 Gamma n A B s :
  pure Gamma ->
  [ Gamma |- TyProd A B s :- Sort U -: U ] ->
  [ A :u Gamma |- n :- B -: s ] ->
  [ Gamma |- Lam n :- TyProd A B s -: U ]
| u_lam2 Gamma n A B s :
  pure Gamma ->
  [ Gamma |- Arrow A B s :- Sort U -: U ] ->
  [ A :l Gamma |- n :- B.[ren (+1)] -: s ] ->
  [ Gamma |- Lam n :- Arrow A B s -: U ]
| l_lam1 Gamma n A B s :
  [ re Gamma |- LnProd A B s :- Sort L -: U ] ->
  [ A :u Gamma |- n :- B -: s ] ->
  [ Gamma |- Lam n :- LnProd A B s -: L ]
| l_lam2 Gamma n A B s :
  [ re Gamma |- Lolli A B s :- Sort L -: U ] ->
  [ A :l Gamma |- n :- B.[ren (+1)] -: s ] ->
  [ Gamma |- Lam n :- Lolli A B s -: L ]
| u_app1 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |- m :- TyProd A B s -: U ] ->
  [ Gamma2 |- n :- A -: U ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- App (Lam B) n -: s ]
| u_app2 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |- m :- Arrow A B s -: U ] ->
  [ Gamma2 |- n :- A -: L ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B -: s ]
| l_app1 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |- m :- LnProd A B s -: L ] ->
  [ Gamma2 |- n :- A -: U ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- App (Lam B) n -: s ]
| l_app2 Gamma1 Gamma2 Gamma A B m n s :
  [ Gamma1 |- m :- Lolli A B s -: L ] ->
  [ Gamma2 |- n :- A -: L ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B -: s ]
| conversion Gamma A B m s :
  A === B ->
  [ Gamma |- m :- A -: s ] ->
  [ Gamma |- m :- B -: s ]
where "[ Gamma |- m :- A -: s ]" := (has_type Gamma m A s).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| u_ok Gamma A :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort U -: U ] ->
  [ A :u Gamma |- ]
| l_ok Gamma A :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort L -: U ] ->
  [ A :l Gamma |- ]
| n_ok Gamma :
  [ Gamma |- ] ->
  [ :n Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Lemma re_ok Gamma :
  [ Gamma |- ] ->
  [ re Gamma |- ].
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
| agree_ren_u Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m :u Gamma) (m.[ren xi] :u Gamma')
| agree_ren_l Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m :l Gamma) (m.[ren xi] :l Gamma')
| agree_ren_n Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (:n Gamma) (:n Gamma')
| agree_ren_wkU Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) (Gamma) (m :u Gamma')
| agree_ren_wkN Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) (Gamma) (:n Gamma').

Lemma agree_ren_refl Gamma :
  agree_ren id Gamma Gamma.
Proof.
  induction Gamma.
  - constructor.
  - destruct a. 
    destruct p.
    destruct s.
    assert (agree_ren id (t :u Gamma) (t :u Gamma)
      = agree_ren (upren id) (t :u Gamma) (t.[ren id] :u Gamma))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (t :l Gamma) (t :l Gamma)
      = agree_ren (upren id) (t :l Gamma) (t.[ren id] :l Gamma))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (:n Gamma) (:n Gamma)
      = agree_ren (upren id) (:n Gamma) (:n Gamma))
      by autosubst.
    rewrite H.
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

Lemma agree_ren_hasU Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  forall x A,
    hasU Gamma x A ->
    hasU Gamma' (xi x) A.[ren xi].
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
    exists (m.[ren xi] :u x).
    exists (m.[ren xi] :u x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren xi] :l x).
    exists (:n x0).
    repeat constructor; eauto.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (:n x).
    exists (m.[ren xi] :l x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (:n x).
    exists (:n x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (m :u x).
    exists (m :u x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (:n x).
    exists (:n x0).
    repeat constructor; eauto.
Qed.

Lemma rename_ok Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  forall Gamma' xi,
    agree_ren xi Gamma Gamma' ->
    [ Gamma' |- m.[ren xi] :- A.[ren xi] -: s ].
Proof.
  intros H.
  induction H; simpl; intros.
  - pose proof (agree_ren_pure H0 H).
    apply axiom; assumption.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply u_prod; eauto.
    replace (Sort s) with ((Sort s).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply l_prod; eauto.
    replace (Sort s) with ((Sort s).[ren (upren xi)]) by autosubst.
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
    eapply agree_ren_hasU; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply l_var.
    eapply agree_ren_hasL; eauto.
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
    eapply u_app1.
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
    apply rename_subst; eauto.
    apply IHhas_type; eauto.
Qed.

Lemma hasU_ok Gamma :
  [ Gamma |- ] ->
  forall x A,
    hasU Gamma x A -> [ re Gamma |- A :- Sort U -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    replace (Sort U) with ((Sort U).[ren (+1)]) by autosubst.
    eapply rename_ok.
    apply H0.
    apply agree_ren_wkU.
    rewrite <- pure_re; eauto.
    apply agree_ren_refl.
    replace (Sort U) with ((Sort U).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkU.
    apply agree_ren_refl.
  - inv H1.
  - inv H0.
    specialize (IHcontext_ok _ _ H2).
    replace (Sort U) with ((Sort U).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma hasR_ok Gamma :
  [ Gamma |- ] ->
  forall x A,
    hasL Gamma x A -> [ re Gamma |- A :- Sort L -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    replace (Sort L) with ((Sort L).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkU.
    apply agree_ren_refl.
  - inv H1; simpl.
    replace (Sort L) with ((Sort L).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
  - inv H0; simpl.
    replace (Sort L) with ((Sort L).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma red_sort_inv s A :
  red (Sort s) A -> A = (Sort s).
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

Lemma value_sound Gamma m A :
  [ Gamma |- m :- A -: U ] -> value m -> pure Gamma.
Proof.
  intros H.
  dependent induction H; intros; eauto.
  - eapply hasU_pure; eauto.
  - inv H2.
  - inv H2.
  - inv H2.
  - inv H2.
Qed.

Lemma weakening_u Gamma m A s B :
  [ Gamma |- m :- A -: s ] ->
  [ B :u Gamma |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkU.
  apply agree_ren_refl.
Qed.

Lemma weakening_n Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  [ :n Gamma |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkN.
  apply agree_ren_refl.
Qed.

Lemma eweakening_u Gamma m m' A A' s B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A -: s ] -> 
  [ B :u Gamma |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakening_u; eauto.
Qed.

Lemma eweakening_n Gamma m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A -: s ] -> 
  [ :n Gamma |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakening_n; eauto.
Qed.

Reserved Notation "[ Delta |- sigma -| Gamma ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil sigma :
  v_subst sigma ->
  [ nil |- sigma -| nil ]
| agree_subst_u Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] :u Delta |- up sigma -| A :u Gamma ]
| agree_subst_l Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] :l Delta |- up sigma -| A :l Gamma ]
| agree_subst_n Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ :n Delta |- up sigma -| :n Gamma ]
| agree_subst_wkU Delta sigma Gamma n A :
  value n ->
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- n :- A.[sigma] -: U ] ->
  [ Delta |- n .: sigma -| A :u Gamma ]
| agree_subst_wkL Delta1 Delta2 Delta sigma Gamma n A :
  value n ->
  merge Delta1 Delta2 Delta ->
  [ Delta1 |- sigma -| Gamma ] ->
  [ Delta2 |- n :- A.[sigma] -: L ] ->
  [ Delta |- n .: sigma -| A :l Gamma ]
| agree_subst_wkN Delta sigma Gamma n :
  value n ->
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- n .: sigma -| :n Gamma ]
| agree_subst_convU Delta sigma Gamma A B :
  A === B ->
  [ Delta |- sigma -| A :u Gamma ] ->
  [ Delta |- sigma -| B :u Gamma ]
| agree_subst_convL Delta sigma Gamma A B :
  A === B ->
  [ Delta |- sigma -| A :l Gamma ] ->
  [ Delta |- sigma -| B :l Gamma ]
where "[ Delta |- sigma -| Gamma ]" := (agree_subst Delta sigma Gamma).

Lemma agree_subst_v_subst Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] -> v_subst sigma.
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
  [ Delta |- sigma -| Gamma ] -> pure Gamma -> pure Delta.
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
  inv H1.
  apply IHagree_subst.
  constructor; eauto.
  inv H1.
Qed.

Lemma agree_subst_refl Gamma :
  [ Gamma |- ids -| Gamma ].
Proof.
  induction Gamma.
  - constructor.
    apply ids_v_subst.
  - destruct a.
    destruct p.
    destruct s.
    replace ([t :u Gamma |- ids -| t :u Gamma])
      with ([t.[ids] :u Gamma |- up ids -| t :u Gamma])
      by autosubst.
    apply agree_subst_u; eauto.
    replace ([t :l Gamma |- ids -| t :l Gamma])
      with ([t.[ids] :l Gamma |- up ids -| t :l Gamma])
      by autosubst.
    apply agree_subst_l; eauto.
    replace (ids) with (up ids) by autosubst.
    apply agree_subst_n; eauto.
Qed.

Lemma agree_subst_hasU Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  forall x A,
    hasU Gamma x A -> 
    [ Delta |- sigma x :- A.[sigma] -: U ].
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
    + eapply eweakening_u; eauto.
      autosubst.
      autosubst.
  - inv H0.
  - inv H0.
    eapply eweakening_n; eauto.
    autosubst.
    autosubst.
  - inv H2; asimpl; eauto.
    pose proof (agree_subst_pure H0 H7).
    pose proof (pure_re H2).
    rewrite H3; eauto.
  - inv H3.
  - inv H1; asimpl; eauto.
  - inv H1.
    + assert (hasU (A :u Gamma) 0 A.[ren (+1)]).
      constructor; eauto.
      eapply conversion.
      eapply conv_subst.
      eapply agree_subst_v_subst; eauto.
      eapply conv_subst.  
      eapply ren_v_subst.
      apply H.
      apply IHagree_subst; eauto.
    + eapply IHagree_subst.
      constructor; eauto.
  - inv H1.
Qed.

Lemma agree_subst_hasL Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  forall x A,
    hasL Gamma x A -> 
    [ Delta |- sigma x :- A.[sigma] -: L ].
Proof.
  induction 1; intros.
  - inv H0.
  - inv H0.
    eapply eweakening_u; eauto.
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
    eapply eweakening_n; eauto.
    autosubst.
    autosubst.
  - inv H2; asimpl; eauto.
  - inv H3; asimpl.
    pose proof (agree_subst_pure H1 H8).
    pose proof (merge_pure1 H0 H3).
    rewrite H4; eauto.
  - inv H1; asimpl; eauto.
  - inv H1.
    apply IHagree_subst.
    constructor; eauto.
  - inv H1.
    assert (hasL (A :l Gamma) 0 A.[ren (+1)]).
    constructor; eauto.
    eapply conversion.
    apply conv_subst.
    eapply agree_subst_v_subst; eauto.
    apply conv_subst.
    apply ren_v_subst.
    apply H.
    apply IHagree_subst; eauto.
Qed.

Lemma agree_subst_re_re Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- sigma -| re Gamma ].
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
    eapply agree_subst_convU.
    apply H.
    apply IHagree_subst.
Qed.

Lemma merge_agree_subst_inv Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  forall Gamma1 Gamma2,
    merge Gamma1 Gamma2 Gamma ->
    exists Delta1 Delta2,
      merge Delta1 Delta2 Delta /\
      [ Delta1 |- sigma -| Gamma1 ] /\
      [ Delta2 |- sigma -| Gamma2 ].
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
    exists (A.[sigma] :u x).
    exists (A.[sigma] :u x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (A.[sigma] :l x).
    exists (:n x0).
    repeat constructor; eauto.
  - pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (:n x).
    exists (A.[sigma] :l x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (:n x).
    exists (:n x0).
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
      eapply agree_subst_wkL.
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
      eapply agree_subst_wkL.
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
  - inv H1.
    assert (merge (A :u Gamma0) (A :u Gamma3) (A :u Gamma)).
    apply merge_left; eauto.
    specialize (IHagree_subst _ _ H1).
    first_order.
    exists x.
    exists x0.
    repeat constructor; eauto.
    eapply agree_subst_convU; eauto.
    eapply agree_subst_convU; eauto.
  - inv H1.
    + assert (merge (A :l Gamma0) (:n Gamma3) (A :l Gamma)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H1).
      first_order.
      exists x.
      exists x0.
      repeat constructor; eauto.
      eapply agree_subst_convL; eauto.
    + assert (merge (:n Gamma0) (A :l Gamma3) (A :l Gamma)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H1).
      first_order.
      exists x.
      exists x0.
      repeat constructor; eauto.
      eapply agree_subst_convL; eauto.
Qed.

Lemma substitution Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  forall Delta sigma,
    [ Delta |- sigma -| Gamma ] ->
    [ Delta |- m.[sigma] :- A.[sigma] -: s ].
Proof.
  intros H.
  dependent induction H; asimpl; intros; eauto.
  - apply axiom.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply u_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
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
  - eapply agree_subst_hasU; eauto.
  - eapply agree_subst_hasL; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3).
    eapply u_lam1; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_l A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    eapply u_lam2; eauto.
    eapply agree_subst_pure; eauto.
    asimpl; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H1).
    specialize (IHhas_type2 _ _ H3).
    eapply l_lam1; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_l A H1).
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
    apply conv_subst; eauto.
    eapply agree_subst_v_subst; eauto.
    apply IHhas_type; eauto.
Qed.

Lemma substitutionU Gamma1 m A B s :
  [ A :u Gamma1 |- m :- B -: s ] ->
  forall Gamma2 Gamma n,
    value n ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |- n :- A -: U ] -> 
    [ Gamma |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  pose proof (value_sound H2 H0).
  pose proof (merge_pure2 H1 H3).
  rewrite H4.
  apply agree_subst_wkU; eauto.
  apply agree_subst_refl.
  pose proof (merge_re_re H1).
  destruct H5.
  asimpl.
  rewrite H5.
  rewrite <- H6.
  rewrite <- pure_re; eauto.
Qed.

Lemma substitutionN Gamma1 m A B s :
  [ :n Gamma1 |- m :- B -: s ] ->
  forall Gamma2 n t,
    value n ->
    [ Gamma2 |- n :- A -: t ] -> 
    [ Gamma1 |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  apply agree_subst_wkN; eauto.
  apply agree_subst_refl.
Qed.

Lemma substitutionL Gamma1 m A B s :
  [ A :l Gamma1 |- m :- B -: s ] ->
  forall Gamma2 Gamma n,
    value n ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |- n :- A -: L ] -> 
    [ Gamma |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  eapply agree_subst_wkL; asimpl; eauto.
  apply agree_subst_refl.
Qed.

Lemma context_convU Gamma m A B C s :
  B === A -> 
  [ A :u Gamma |- m :- C -: s ] -> 
  [ B :u Gamma |- m :- C -: s ].
Proof.
  move=> conv tp. 
  cut ([ B :u Gamma |- m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp.
  eapply agree_subst_convU; simpl.
  apply conv.
  apply agree_subst_refl.
Qed.

Lemma context_convL Gamma m A B C s :
  B === A -> 
  [ A :l Gamma |- m :- C -: s ] -> 
  [ B :l Gamma |- m :- C -: s ].
Proof.
  move=> conv tp. 
  cut ([ B :l Gamma |- m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp.
  eapply agree_subst_convL; simpl.
  apply conv.
  apply agree_subst_refl.
Qed.

Lemma sort_inj s1 s2 :
  Sort s1 === Sort s2 -> s1 = s2.
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

Lemma tyProd_inv Gamma A B s :
  [ re Gamma |- TyProd A B s :- Sort U -: U ] -> 
  [ re Gamma |- A :- Sort U -: U ] /\ [ A :u re Gamma |- B :- Sort s -: U ].
Proof.
  move e:(TyProd A B s) => n tp. elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s p tp1 _ tp2 _ A0 B0 s0 [->->->] => //.
Qed.

Lemma arrow_inv Gamma A B s :
  [ re Gamma |- Arrow A B s :- Sort U -: U ] ->
  [ re Gamma |- A :- Sort L -: U ] /\ [ re Gamma |- B :- Sort s -: U ].
Proof.
  move e:(Arrow A B s) => n tp. elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s p tp1 _ tp2 _ A0 B0 s0 [->->->] => //.
Qed.

Lemma lnProd_inv Gamma A B s :
  [ re Gamma |- LnProd A B s :- Sort L -: U ] ->
  [ re Gamma |- A :- Sort U -: U ] /\ [ A :u re Gamma |- B :- Sort s -: U ].
Proof.
  move e:(LnProd A B s) => n tp. elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s p tp1 _ tp2 _ A0 B0 s0 [->->->] => //.
Qed.

Lemma lolli_inv Gamma A B s :
  [ re Gamma |- Lolli A B s :- Sort L -: U ] ->
  [ re Gamma |- A :- Sort L -: U ] /\ [ re Gamma |- B :- Sort s -: U ].
Proof.
  move e:(Lolli A B s) => n tp. elim: tp A B s e => //{Gamma n}.
  move=> Gamma A B s p tp1 _ tp2 _ A0 B0 s0 [->->->] => //.
  move=> Gamma A B m s p tp ih A0 B0 s0 e.
  apply ih in e.
  first_order; eauto.
  eapply conversion.
  apply p.
  apply H.
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

Lemma u_lam1_inv Gamma n C :
  [ Gamma |- Lam n :- C -: U ] -> 
  forall A B s, 
    (C === TyProd A B s) ->
    [ A :u Gamma |- n :- B -: s ].
Proof.
  intros.
  dependent induction H.
  + apply tyProd_inj in H2.
    first_order.
    eapply conversion.
    apply H3.
    eapply context_convU.
    apply conv_sym; apply H2.
    rewrite <- H4; eauto.
  + exfalso; solve_conv.
  + apply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H1.
Qed.

Lemma u_lam2_inv Gamma n C :
  [ Gamma |- Lam n :- C -: U ] -> 
  forall A B s, 
    (C === Arrow A B s) ->
    [ A :l Gamma |- n :- B.[ren (+1)] -: s ].
Proof.
  intros.
  dependent induction H.
  + exfalso; solve_conv.
  + apply arrow_inj in H2.
    first_order.
    eapply conversion.
    apply conv_subst.
    apply ren_v_subst.
    apply H3.
    eapply context_convL.
    apply conv_sym; apply H2.
    rewrite <- H4; eauto.
  + apply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H1.
Qed.

Lemma l_lam1_inv Gamma n C :
  [ Gamma |- Lam n :- C -: L ] -> 
  forall A B s, 
    (C === LnProd A B s) ->
    [ A :u Gamma |- n :- B -: s ].
Proof.
  intros.
  dependent induction H.
  + apply lnProd_inj in H1.
    first_order.
    eapply conversion.
    apply H2.
    eapply context_convU.
    apply conv_sym; apply H1.
    rewrite <- H3; eauto.
  + solve_conv; exfalso; eauto.
  + apply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H1.
Qed.

Lemma l_lam2_inv Gamma n C :
  [ Gamma |- Lam n :- C -: L ] -> 
  forall A B s, 
    (C === Lolli A B s) ->
    [ A :l Gamma |- n :- B.[ren (+1)] -: s ].
Proof.
  intros.
  dependent induction H.
  + exfalso; solve_conv.
  + apply lolli_inj in H1.
    first_order.
    eapply conversion.
    apply conv_subst.
    apply ren_v_subst.
    apply H2.
    eapply context_convL.
    apply conv_sym; apply H1.
    rewrite <- H3; eauto.
  + apply IHhas_type; eauto.
    eapply conv_trans.
    apply H.
    apply H1.
Qed.

Theorem preservation Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  forall n, pstep m n -> 
    [ Gamma |- n :- A -: s ].
Proof.
  intros.
  dependent induction H.
  - inv H0.
    apply axiom; eauto.
  - inv H2.
    specialize (IHhas_type1 _ H7).
    specialize (IHhas_type2 _ H8).
    apply u_prod; eauto.
    eapply context_convU.
    eapply conv1i; eauto.
    apply IHhas_type2.
  - inv H2.
    specialize (IHhas_type1 _ H7).
    specialize (IHhas_type2 _ H8).
    apply l_prod; eauto.
    eapply context_convU.
    eapply conv1i; eauto.
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
      eapply substitutionU.
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
      eapply substitutionL.
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
      eapply substitutionU.
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
      eapply substitutionL.
      apply IHhas_type1.
      eapply pstep_value; eauto.
      apply H1.
      apply IHhas_type2.
  - eapply conversion; eauto.
Qed.

Corollary preservation_step m n :
  step m n ->
  forall Gamma A s,
    [ Gamma |- m :- A -: s ] ->
    [ Gamma |- n :- A -: s ].
Proof.
  intros.
  eapply preservation.
  apply H0.
  apply step_pstep; eauto.
Qed.

Corollary preservation_star_step m n :
  star step m n ->
  forall Gamma A s,
    [ Gamma |- m :- A -: s ] ->
    [ Gamma |- n :- A -: s ].
Proof.
  intro H.
  dependent induction H; intros; eauto.
  eapply preservation.
  apply IHstar; eauto.
  apply step_pstep; eauto.
Qed.

Lemma canonical_tyProd m C :
  [ nil |- m :- C -: U ] -> value m ->
  forall A B s, 
    C === TyProd A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - inv H.
  - exists n; eauto.
  - exfalso; solve_conv.
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
  [ nil |- m :- C -: L ] -> value m ->
  forall A B s, 
    C === LnProd A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - inv H.
  - exists n; eauto.
  - exfalso; solve_conv.
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
  [ nil |- m :- C -: U ] -> value m ->
  forall A B s, 
    C === Arrow A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - exfalso; solve_conv.
  - inv H.
  - exfalso; solve_conv.
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
  [ nil |- m :- C -: L ] -> value m ->
  forall A B s, 
    C === Lolli A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H.
  - inv H.
  - exfalso; solve_conv.
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
  [ nil |- m :- A -: s ] -> value m \/ exists n, step m n.
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