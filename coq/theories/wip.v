From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program.
Require Import AutosubstSsr ARS cc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CLC.

Declare Scope clc_scope.
Open Scope clc_scope.

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

Lemma merge_re_re_re T (Gamma : context T) :
  merge (re Gamma) (re Gamma) (re Gamma).
Proof.
  induction Gamma; intros.
  constructor.
  destruct a.
  destruct p.
  destruct s.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
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
| Var  (x : var)
| Sort (s : sort) (l : option nat)
| Prod (A : term) (s : sort)
       (B : {bind term}) (t : sort)
| Lam  (n : {bind term})
| App  (m n : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort srt l   : value (Sort srt l)
| value_var x        : value (Var x)
| value_prod A s B t : value (Prod A s B t)
| value_lam n        : value (Lam n).

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
| pstep_beta m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam m) n) (m'.[n'/])
| pstep_prod A A' s B B' t :
  pstep A A' ->
  pstep B B' ->
  pstep (Prod A s B t) 
        (Prod A' s B' t).

Notation red := (star pstep).
Notation "m === n" := (conv pstep m n) (at level 50).

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.

Lemma step_pstep n n' : step n n' -> pstep n n'.
Proof with eauto using pstep, pstep_refl.
  intros.
  induction H...
Qed.

Lemma pstep_subst s t : 
  pstep s t -> 
    forall sigma, pstep s.[sigma] t.[sigma].
Proof with eauto using pstep, pstep_refl.
  intros.
  dependent induction H...
  - asimpl.
    specialize (IHpstep1 (up sigma)).
    specialize (IHpstep2 (sigma)).
    pose proof (pstep_beta IHpstep1 IHpstep2).
    asimpl in H1; eauto.
Qed.

Lemma red_subst s t : 
  red s t -> 
    forall sigma, red s.[sigma] t.[sigma].
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
Qed.

Lemma pstep_compat s t :
  pstep s t ->
    forall sigma tau, 
      psstep sigma tau -> pstep s.[sigma] t.[tau].
Proof with eauto 6 using pstep, psstep_up.
  intros.
  dependent induction H; asimpl...
  - pose proof (psstep_up H1).
    pose proof (IHpstep1 _ _ H2).
    pose proof (IHpstep2 _ _ H1).
    pose proof (pstep_beta H3 H4).
    asimpl in H5; eauto.
Qed.

Lemma psstep_compat s1 s2 sigma tau:
  psstep sigma tau -> pstep s1 s2 -> psstep (s1 .: sigma) (s2 .: tau).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep, pstep_refl.
  intros.
  apply pstep_compat...
  - apply psstep_compat...
    apply psstep_refl.
Qed.

Lemma pstep_compat_beta m m' :
  pstep m m' -> 
    forall n n',
      pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using psstep_refl, psstep_compat.
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
      assert (pstep (Lam m0) (Lam m'0))...
      apply (IHpstep1) in H.  apply (IHpstep2) in H6. first_order.
      inv H.
      inv H3.
      exists (n'2.[x0/]). split.
      apply pstep_beta...
      apply pstep_compat_beta...
  - inv H1.
    + inv H4.
      apply IHpstep1 in H2. apply IHpstep2 in H6. first_order.
      exists (x.[x0/]). split.
      * apply pstep_compat_beta...
      * apply pstep_beta...
    + apply IHpstep1 in H4. apply IHpstep2 in H6. first_order.
      exists (x0.[x/]). split.
      * apply pstep_compat_beta...
      * apply pstep_compat_beta...
  - inv H1. apply (IHpstep1) in H7. apply (IHpstep2) in H8.
    first_order. exists (Prod x0 s x t)...
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

Lemma conv_prod A A' s B B' t :
  A === A' -> B === B' -> Prod A s B t === Prod A' s B' t.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Prod A' s B t)).
  - apply: (conv_hom (((Prod^~ s)^~ B)^~ t)) conv1 => x y ps.
    constructor; eauto.
    apply pstep_refl.
  - apply: (conv_hom ((Prod A' s)^~ t)) conv2 => x y ps.
    constructor; eauto.
    apply pstep_refl.
Qed.

Lemma conv_subst sigma s t : 
  s === t -> s.[sigma] === t.[sigma].
Proof. 
  intro H.
  eapply conv_hom; eauto.
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

Lemma prod_ren_inv A s B t v xi :
  Prod A s B t = v.[ren xi] -> 
  exists A s B t, v = Prod A s B t.
Proof.
  induction v; asimpl; try discriminate; eauto 6.
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
  apply prod_ren_inv in x; first_order; subst; constructor.
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
    destruct m1; asimpl; try discriminate. inv H3.
    assert (n.[up (ren xi)] = n.[ren (upren xi)]) by autosubst.
    pose proof (left_invertible_upren H1).
    pose proof (IHpstep1 n (upren xi) H2 H3).
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    pose proof (IHpstep2 m2 xi H5 H1).
    firstorder; subst; asimpl.
    exists (x1.[x .: ids]); asimpl.
    firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m.[ren xi] = m.[ren xi]) by eauto.
    assert (B0.[up (ren xi)] = B0.[ren (upren xi)]) by autosubst.
    assert (left_invertible (upren xi)).
    apply left_invertible_upren; eauto.
    apply IHpstep1 in H2; eauto.
    apply IHpstep2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (Prod x0 s0 x1 t0); asimpl; firstorder.
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

Lemma red_prod_inv A B s t x :
  red (Prod A s B t) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Prod A' s B' t.
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

Lemma prod_inj A A' s s' B B' t t' :
  Prod A s B t === Prod A' s' B' t' ->
  A === A' /\ B === B' /\ s = s' /\ t = t'.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_prod_inv in H0.
  apply red_prod_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
  inv H2; eauto.
Qed.

Ltac red_inv m H :=
  match m with
  | Var  => apply red_var_inv in H
  | Sort => apply red_sort_inv in H
  | Prod => apply red_prod_inv in H
  | Lam  => apply red_lam_inv in H
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
  | [ H : red (?m _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
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

Notation "s @ l" := (Sort s (Some l)) (at level 30).
Notation prop s := (Sort s None).

Inductive sub1 : term -> term -> Prop :=
| sub1_refl A : 
  sub1 A A
| sub1_prop s l : 
  sub1 (prop s) (s @ l)
| sub1_sort s l1 l2 : 
  l1 <= l2 -> 
  sub1 (s @ l1) (s @ l2)
| sub1_prod A s B1 B2 t : 
  sub1 B1 B2 -> 
  sub1 (Prod A s B1 t) (Prod A s B2 t).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : 
  sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 50, no associativity) : clc_scope.

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_prop s n : prop s <: s @ n.
Proof. exact/sub1_sub/sub1_prop. Qed.

Lemma sub_sort s n m : n <= m -> s @ n <: s @ m.
Proof. move=> leq. exact/sub1_sub/sub1_sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto 6 using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D => {A B}
    [ A C D 
    | s l C D conv sb
    | s l1 l2 leq C D conv sb
    | A s B1 B2 t sb1 ih C D conv sb2]...
  - inv sb; try (exfalso; solve_conv)...
    move: conv => /sort_inj [->[eq]].
    apply: sub_prop.
  - inv sb; try (exfalso; solve_conv)...
    move: conv => /sort_inj [->[eq]].
    apply: sub_sort. subst.
    exact: leq_trans leq _.
  - inv sb2; try (exfalso; solve_conv)...
    move: conv => /prod_inj[conv1 [conv2 [->->]]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    eapply SubI. 
    eapply sub1_prod... 
    eapply conv_prod... 
    exact: conv_prod.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_prop_inv s1 s2 :
  prop s1 <: prop s2 -> s1 = s2.
Proof.
  move=> [s1' s2' []].
  - move=> A c1 c2.
    have{c1 c2}/sort_inj[s l]: prop s1 === prop s2.
     exact: conv_trans c2.
     exact: s.
  - move=> s l /sort_inj[-> _] /sort_inj[-> _] => //.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_sort_inv s1 s2 l1 l2 :
  s1 @ l1 <: s2 @ l2 -> s1 = s2 /\ l1 <= l2.
Proof.
  move=> [s1' s2' []].
  - move=> A c1 c2.
    have{c1 c2}/sort_inj[s l]: s1 @ l1 === s2 @ l2.
     exact: conv_trans c2.
    inv l=> //.
  - move=> s l0 /sort_inj[_ h] => //.
  - move=> s l0 l3 leq /sort_inj[->[->]] /sort_inj[<-[<-]] => //.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_prod_inv A1 A2 s1 s2 B1 B2 t1 t2 :
  Prod A1 s1 B1 t1 <: Prod A2 s2 B2 t2 -> 
  A1 === A2 /\ B1 <: B2 /\ s1 = s2 /\ t1 = t2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/prod_inj[c1 [c2 [->->]]]: 
      Prod A1 s1 B1 t1 === Prod A2 s2 B2 t2.
     exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> A s B0 B3 t sb /prod_inj[c1 [c2 [<-<-]]]. 
    move=> /prod_inj[c3 [c4 [->->]]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst sigma A B : sub1 A B -> sub1 A.[sigma] B.[sigma].
Proof. move=> s. elim: s sigma => /=; eauto using sub1. Qed.

Lemma sub_subst sigma A B : A <: B -> A.[sigma] <: B.[sigma].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Lemma sub_ren A B xi : A <: B -> A.[ren xi] <: B.[ren xi].
Proof.
  intros.
  apply sub_subst; eauto.
Qed.

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- m :- A -: s ]".
  
Inductive has_type : context term -> term -> term -> sort -> Prop :=
| p_axiom Gamma : 
  pure Gamma ->
  [ Gamma |- prop U :- U @ 0 -: U ]
| s_axiom Gamma s l : 
  pure Gamma ->
  [ Gamma |- s @ l :- U @ l.+1 -: U ]
| u_prop Gamma A B l :
  pure Gamma ->
  [ Gamma |- A :- Sort U l -: U ] ->
  [ A :u Gamma |- B :- prop U -: U ] ->
  [ Gamma |- Prod A U B U :- prop U -: U ]
| u_prod Gamma A B s t l :
  pure Gamma ->
  [ Gamma |- A :- U @ l -: U ] ->
  [ A :u Gamma |- B :- s @ l -: U ] ->
  [ Gamma |- Prod A U B s :- t @ l -: U ]
| l_prod Gamma A B s t l :
  pure Gamma ->
  [ Gamma |- A :- L @ l -: U ] ->
  [ :n Gamma |- B :- s @ l -: U ] ->
  [ Gamma |- Prod A L B s :- t @ l -: U ]
| u_var Gamma x A : 
  hasU Gamma x A ->
  [ Gamma |- Var x :- A -: U ]
| l_var Gamma x A :
  hasL Gamma x A ->
  [ Gamma |- Var x :- A -: L ]
| u_lam Gamma n A s B t l :
  pure Gamma ->
  [ Gamma |- Prod A s B t :- Sort U l -: U ] ->
  [ A :[s] Gamma |- n :- B -: t ] ->
  [ Gamma |- Lam n :- Prod A s B t -: U ]
| l_lam Gamma n A s B t l :
  [ re Gamma |- Prod A s B t :- L @ l -: U ] ->
  [ A :[s] Gamma |- n :- B -: t ] ->
  [ Gamma |- Lam n :- Prod A s B t -: L ]
| u_app Gamma1 Gamma2 Gamma A B s t m n :
  pure Gamma2 ->
  [ Gamma1 |- m :- Prod A U B s -: t ] ->
  [ Gamma2 |- n :- A -: U ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B.[n/] -: s ]
| l_app Gamma1 Gamma2 Gamma A B s t m n :
  [ Gamma1 |- m :- Prod A L B s -: t ] ->
  [ Gamma2 |- n :- A -: L ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B.[n/] -: s ]
| conversion Gamma A B m s l :
  A <: B ->
  [ re Gamma |- B :- Sort s l -: U ] ->
  [ Gamma |- m :- A -: s ] ->
  [ Gamma |- m :- B -: s ]
where "[ Gamma |- m :- A -: s ]" := (has_type Gamma m A s).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| u_ok Gamma A l :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort U l -: U ] ->
  [ A :u Gamma |- ]
| l_ok Gamma A l :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort L l -: U ] ->
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
    apply p_axiom; assumption.
  - pose proof (agree_ren_pure H0 H).
    apply s_axiom; assumption.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply u_prop; eauto.
    replace (prop U) with ((prop U).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply u_prod; eauto.
    replace (s @ l) with ((s @ l).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply l_prod; eauto.
    replace (s @ l) with ((s @ l).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply u_var.
    eapply agree_ren_hasU; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply l_var.
    eapply agree_ren_hasL; eauto.
  - eapply u_lam.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    asimpl.
    apply IHhas_type2; eauto.
    destruct s; constructor; eauto.
  - eapply l_lam.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    asimpl.
    apply IHhas_type2.
    destruct s; constructor; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H3 H2).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    pose proof (agree_ren_pure H6 H).
    eapply u_app; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    eapply l_app; eauto.
  - eapply conversion.
    apply sub_ren; eauto.
    apply IHhas_type1.
    apply agree_ren_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma hasU_ok Gamma :
  [ Gamma |- ] ->
  forall x A,
    hasU Gamma x A ->
    exists l, [ re Gamma |- A :- Sort U l -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    exists l.
    replace (Sort U l) with ((Sort U l).[ren (+1)]) by autosubst.
    eapply rename_ok.
    apply H0.
    apply agree_ren_wkU.
    rewrite <- pure_re; eauto.
    apply agree_ren_refl.
    specialize (IHcontext_ok _ _ H6).
    inv IHcontext_ok.
    exists x.
    replace (Sort U x) with ((Sort U x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkU.
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

Lemma hasL_ok Gamma :
  [ Gamma |- ] ->
  forall x A,
    hasL Gamma x A ->
    exists l, [ re Gamma |- A :- Sort L l -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    specialize (IHcontext_ok _ _ H6).
    inv IHcontext_ok.
    exists x.
    replace (Sort L x) with ((Sort L x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkU.
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

Lemma weakeningU Gamma m A s B :
  [ Gamma |- m :- A -: s ] ->
  [ B :u Gamma |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkU.
  apply agree_ren_refl.
Qed.

Lemma weakeningN Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  [ :n Gamma |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkN.
  apply agree_ren_refl.
Qed.

Lemma eweakeningU Gamma m m' A A' s B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A -: s ] -> 
  [ B :u Gamma |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakeningU; eauto.
Qed.

Lemma eweakeningN Gamma m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A -: s ] -> 
  [ :n Gamma |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakeningN; eauto.
Qed.

Reserved Notation "[ Delta |- sigma -| Gamma ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil sigma :
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
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- n :- A.[sigma] -: U ] ->
  [ Delta |- n .: sigma -| A :u Gamma ]
| agree_subst_wkL Delta1 Delta2 Delta sigma Gamma n A :
  merge Delta1 Delta2 Delta ->
  [ Delta1 |- sigma -| Gamma ] ->
  [ Delta2 |- n :- A.[sigma] -: L ] ->
  [ Delta |- n .: sigma -| A :l Gamma ]
| agree_subst_wkN Delta sigma Gamma n :
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- n .: sigma -| :n Gamma ]
| agree_subst_convU Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[sigma] :- Sort U l -: U ] ->
  [ Delta |- sigma -| A :u Gamma ] ->
  [ Delta |- sigma -| B :u Gamma ]
| agree_subst_convL Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[sigma] :- Sort L l -: U ] ->
  [ re Gamma |- B :- Sort L l -: U ] ->
  [ Delta |- sigma -| A :l Gamma ] ->
  [ Delta |- sigma -| B :l Gamma ]
where "[ Delta |- sigma -| Gamma ]" := (agree_subst Delta sigma Gamma).

Lemma agree_subst_pure Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] -> pure Gamma -> pure Delta.
Proof.
  induction 1; intros; eauto.
  inv H0.
  constructor; eauto.
  inv H0.
  inv H0.
  constructor; eauto.
  inv H1; eauto.
  inv H2.
  inv H0; eauto.
  inv H2.
  apply IHagree_subst.
  constructor; eauto.
  inv H3.
Qed.

Lemma agree_subst_refl Gamma :
  [ Gamma |- ids -| Gamma ].
Proof.
  induction Gamma.
  - constructor.
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
  - inv H.
  - inv H0.
    + asimpl.
      apply u_var.
      replace (A.[sigma >> ren (+1)]) 
        with (A.[sigma].[ren (+1)]) by autosubst.
      constructor.
      eapply agree_subst_pure; eauto.
    + eapply eweakeningU; eauto.
      autosubst.
      autosubst.
  - inv H0.
  - inv H0.
    eapply eweakeningN; eauto.
    autosubst.
    autosubst.
  - inv H1; asimpl; eauto.
    pose proof (agree_subst_pure H H6).
    pose proof (pure_re H1).
    rewrite H2; eauto.
  - inv H2.
  - inv H0; asimpl; eauto.
  - inv H2.
    + assert (hasU (A :u Gamma) 0 A.[ren (+1)]).
      constructor; eauto.
      eapply conversion.
      eapply sub_subst.
      eapply sub_ren; eauto.
      apply H0.
      apply IHagree_subst; eauto.
    + eapply IHagree_subst.
      constructor; eauto.
  - inv H3.
Qed.

Lemma agree_subst_hasL Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  forall x A,
    hasL Gamma x A -> 
    [ Delta |- sigma x :- A.[sigma] -: L ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H0.
    eapply eweakeningU; eauto.
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
    eapply eweakeningN; eauto.
    autosubst.
    autosubst.
  - inv H1; asimpl; eauto.
  - inv H2; asimpl.
    pose proof (agree_subst_pure H0 H7).
    pose proof (merge_pure1 H H2).
    rewrite H3; eauto.
  - inv H0; asimpl; eauto.
  - inv H2.
    apply IHagree_subst.
    constructor; eauto.
  - inv H3.
    assert (hasL (A :l Gamma) 0 A.[ren (+1)]).
    constructor; eauto.
    eapply conversion.
    apply sub_subst.
    apply sub_ren; eauto.
    apply H0.
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
    pose proof (merge_re_re H).
    destruct H2.
    rewrite <- H2; eauto.
  - constructor; eauto.
  - simpl in IHagree_subst.
    eapply agree_subst_convU.
    apply H.
    rewrite <- re_re.
    apply H0.
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
  - inv H.
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
  - inv H1.
    pose proof (IHagree_subst _ _ H5).
    first_order.
    exists x.
    exists x0.
    pose proof (merge_re_re H1).
    destruct H4.
    repeat constructor; eauto.
    rewrite H4; eauto.
    rewrite H6; eauto.
  - inv H2.
    + pose proof (IHagree_subst _ _ H6).
      firstorder.
      pose proof (merge_split1 H H2).
      firstorder.
      exists x1.
      exists x0.
      firstorder.
      eapply agree_subst_wkL; eauto.
      eapply agree_subst_wkN; eauto.
    + pose proof (IHagree_subst _ _ H6).
      firstorder.
      pose proof (merge_split2 H H2).
      firstorder.
      exists x.
      exists x1.
      firstorder.
      apply agree_subst_wkN; eauto.
      eapply agree_subst_wkL; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists x.
    exists x0.
    repeat constructor; eauto.
  - inv H2.
    assert (merge (A :u Gamma0) (A :u Gamma3) (A :u Gamma)).
    apply merge_left; eauto.
    specialize (IHagree_subst _ _ H2).
    first_order.
    exists x.
    exists x0.
    pose proof (merge_re_re H3).
    inv H7.
    repeat constructor; eauto.
    eapply agree_subst_convU; eauto.
    rewrite H8; eauto.
    eapply agree_subst_convU; eauto.
    rewrite H9; eauto.
  - inv H3.
    + assert (merge (A :l Gamma0) (:n Gamma3) (A :l Gamma)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H3).
      first_order.
      exists x.
      exists x0.
      pose proof (merge_re_re H4). inv H8.
      pose proof (merge_re_re H7). inv H8.
      repeat constructor; eauto.
      eapply agree_subst_convL; eauto.
      rewrite H9; eauto.
      rewrite H11; eauto.
    + assert (merge (:n Gamma0) (A :l Gamma3) (A :l Gamma)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H3).
      first_order.
      exists x.
      exists x0.
      pose proof (merge_re_re H4). inv H8.
      pose proof (merge_re_re H7). inv H8.
      repeat constructor; eauto.
      eapply agree_subst_convL; eauto.
      rewrite H10; eauto.
      rewrite H12; eauto.
Qed.

Lemma substitution Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  forall Delta sigma,
    [ Delta |- sigma -| Gamma ] ->
    [ Delta |- m.[sigma] :- A.[sigma] -: s ].
Proof.
  intros H.
  dependent induction H; asimpl; intros; eauto.
  - apply p_axiom.
    eapply agree_subst_pure; eauto.
  - apply s_axiom.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    eapply u_prop; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply u_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_n H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply l_prod; eauto.
    eapply agree_subst_pure; eauto.
  - eapply agree_subst_hasU; eauto.
  - eapply agree_subst_hasL; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    destruct s.
    + pose proof (agree_subst_u A H2).
      specialize (IHhas_type2 _ _ H3).
      eapply u_lam; eauto.
      eapply agree_subst_pure; eauto.
    + pose proof (agree_subst_l A H2).
      specialize (IHhas_type2 _ _ H3).
      eapply u_lam; eauto.
      eapply agree_subst_pure; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    destruct s.
    + pose proof (agree_subst_u A H1).
      specialize (IHhas_type2 _ _ H3).
      eapply l_lam; eauto.
    + pose proof (agree_subst_l A H1).
      specialize (IHhas_type2 _ _ H3).
      eapply l_lam; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H3 H2).
    first_order.
    pose proof (agree_subst_pure H6 H).
    pose proof (u_app H7 IHhas_type1 IHhas_type2 H4).
    asimpl in H8; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    pose proof (l_app IHhas_type1 IHhas_type2 H3).
    asimpl in H6; eauto.
  - eapply conversion.
    apply sub_subst; eauto.
    apply IHhas_type1; eauto.
    apply agree_subst_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma substitutionU Gamma1 m A B s :
  [ A :u Gamma1 |- m :- B -: s ] ->
  forall Gamma2 Gamma n,
    pure Gamma2 ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |- n :- A -: U ] -> 
    [ Gamma |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  pose proof (merge_pure2 H1 H0).
  rewrite H3.
  apply agree_subst_wkU; eauto.
  apply agree_subst_refl.
  pose proof (merge_re_re H1).
  destruct H4.
  asimpl.
  rewrite H4.
  rewrite <- H5.
  rewrite <- pure_re; eauto.
Qed.

Lemma substitutionN Gamma1 m A B s :
  [ :n Gamma1 |- m :- B -: s ] ->
  forall Gamma2 n t,
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

Lemma context_convU Gamma m A B C s l :
  B === A -> 
  [ re Gamma |- A :- Sort U l -: U ] ->
  [ A :u Gamma |- m :- C -: s ] -> 
  [ B :u Gamma |- m :- C -: s ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B :u Gamma |- m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp2.
  eapply agree_subst_convU; simpl.
  eapply conv_sub; eauto.
  pose proof (weakeningU B tp1).
  asimpl.
  asimpl in H.
  apply H.
  apply agree_subst_refl.
Qed.

Lemma context_convL Gamma m A B C s l :
  B === A -> 
  [ re Gamma |- A :- Sort L l -: U ] ->
  [ A :l Gamma |- m :- C -: s ] -> 
  [ B :l Gamma |- m :- C -: s ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B :l Gamma |- m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp2.
  eapply agree_subst_convL; simpl.
  eapply conv_sub; eauto.
  pose proof (weakeningN tp1).
  asimpl.
  asimpl in H.
  apply H.
  apply tp1.
  apply agree_subst_refl.
Qed.

Ltac solve_sub :=
  match goal with
  | [ H : _ <: _ |- _ ] =>
    let A := fresh "A" in
    let B := fresh "B" in
    let sb := fresh "sb" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    destruct H as [A B sb c1 c2]; destruct sb
  end;
  match goal with
  | [ c1 : ?A === ?x, c2 : ?x === ?B |- _ ] => 
    assert (A === B) by 
      (eapply conv_trans; try solve [apply c1| apply c2]);
    clear c1 c2;
    solve_conv
  | _ => solve_conv
  end.

Lemma u_prod_inv Gamma A B s srt :
  [ re Gamma |- Prod A U B s :- srt -: U ] -> 
  exists l,
    [ re Gamma |- A :- Sort U l -: U ] /\ 
    [ A :u re Gamma |- B :- Sort s l -: U ].
Proof.
  move e:(Prod A U B s) => n tp. 
  elim: tp A B s e => //{Gamma n srt}.
  - move=> Gamma A B l p tp1 _ tp2 _ A0 B0 s [->->->].
    exists l; firstorder.
    destruct l; eauto.
    assert (prop U <: U @ n).
    apply sub_prop.
    eapply conversion; eauto.
    constructor; apply re_pure.
  - move=> Gamma A B s _ l p tp1 _ pt2 _ A0 B0 s0 [->->->].
    exists (Some l); eauto.
Qed.

Lemma l_prod_inv Gamma A B s srt :
  [ re Gamma |- Prod A L B s :- srt -: U ] -> 
  exists l,
    [ re Gamma |- A :- Sort L l -: U ] /\ 
    [ :n re Gamma |- B :- Sort s l -: U ].
Proof.
  move e:(Prod A L B s) => n tp. 
  elim: tp A B s e => //{Gamma n srt}.
  - move=> Gamma A B s _ l p tp1 _ pt2 _ A0 B0 s0 [->->->].
    exists (Some l); eauto.
Qed.

Lemma l_prod_falseX Gamma A B s srt :
  [ re Gamma |- Prod A L B s :- srt -: U ] ->
  srt <: prop U -> False.
Proof.
  intro h.
  dependent induction h; intros.
  - exfalso; solve_sub.
  - eapply IHh2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma l_prod_false Gamma A B s :
  ~[ re Gamma |- Prod A L B s :- prop U -: U ].
Proof.
  intro h.
  eapply l_prod_falseX; eauto.
Qed.

Lemma u_lam_invX Gamma n C srt :
  [ Gamma |- Lam n :- C -: srt ] -> 
  forall A B s l, 
    (C <: Prod A U B s /\ [A :u re Gamma |- B :- Sort s l -: U]) ->
    [ A :u Gamma |- n :- B -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  + pose proof (sub_prod_inv H2).
    first_order; subst.
    pose proof (pure_re H).
    rewrite H6 in H0.
    apply u_prod_inv in H0. inv H0.
    eapply conversion; eauto.
    eapply context_convU.
    apply conv_sym; apply H4.
    apply H7.
    apply H1.
  + pose proof (sub_prod_inv H1).
    first_order; subst.
    apply u_prod_inv in H. inv H.
    eapply conversion; eauto.
    eapply context_convU.
    apply conv_sym; apply H3.
    apply H5.
    apply H0.
  + eapply IHhas_type2; eauto.
    split.
    eapply sub_trans; eauto.
    apply H3.
Qed.

Lemma u_lam_inv Gamma n A B s t l :
  [ re Gamma |- Prod A U B s :- Sort t l -: U ] ->
  [ Gamma |- Lam n :- Prod A U B s -: t ] -> 
  [ A :u Gamma |- n :- B -: s ].
Proof.
  intros.
  apply u_prod_inv in H; inv H; firstorder.
  eapply u_lam_invX; eauto.
Qed.

Lemma l_lam_invX Gamma n C srt :
  [ Gamma |- Lam n :- C -: srt ] -> 
  forall A B s l, 
    (C <: Prod A L B s /\ [:n re Gamma |- B :- Sort s l -: U]) ->
    [ A :l Gamma |- n :- B -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  + pose proof (sub_prod_inv H2).
    first_order; subst.
    pose proof (pure_re H).
    rewrite H6 in H0.
    apply l_prod_inv in H0. inv H0.
    eapply conversion; eauto.
    eapply context_convL.
    apply conv_sym; apply H4.
    apply H7.
    apply H1.
  + pose proof (sub_prod_inv H1).
    first_order; subst.
    apply l_prod_inv in H. inv H.
    eapply conversion; eauto.
    eapply context_convL.
    apply conv_sym; apply H3.
    apply H5.
    apply H0.
  + eapply IHhas_type2; eauto.
    split.
    eapply sub_trans; eauto.
    apply H3.
Qed.

Lemma l_lam_inv Gamma n A B s t l :
  [ re Gamma |- Prod A L B s :- Sort t l -: U ] ->
  [ Gamma |- Lam n :- Prod A L B s -: t ] -> 
  [ A :l Gamma |- n :- B -: s ].
Proof.
  intros.
  apply l_prod_inv in H; inv H; firstorder.
  eapply l_lam_invX; eauto.
Qed.

Lemma merge_context_ok_inv Gamma Gamma1 Gamma2 :
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- ] ->
  [ Gamma1 |- ] /\ [ Gamma2 |- ].
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
  [ Gamma |- ] ->
  [ Gamma |- m :- A -: s ] ->
  exists l, [ re Gamma |- A :- Sort s l -: U ].
Proof.
  intros.
  dependent induction H0.
  - exists (Some 1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some l.+2).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some 0).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - eapply hasU_ok; eauto.
  - eapply hasL_ok; eauto.
  - exists l.
    rewrite <- pure_re; eauto.
  - exists (Some l); eauto.
  - pose proof (merge_pure2 H1 H0).
    pose proof (merge_re_re H1). inv H3.
    apply merge_context_ok_inv in H1; eauto. inv H1.
    apply IHhas_type1 in H2. inv H2.
    apply u_prod_inv in H1. first_order.
    exists x0.
    replace (Sort s x0) with ((Sort s x0).[n/]) by autosubst.
    eapply substitutionU; eauto.
    replace (Gamma2) with (re Gamma1).
    apply merge_re_re_re.
    apply pure_re in H0.
    rewrite H0.
    rewrite H5; eauto.
  - pose proof (merge_re_re H0). inv H1.
    apply merge_context_ok_inv in H0; eauto. inv H0.
    apply IHhas_type1 in H1. inv H1.
    eapply l_prod_inv in H0; eauto; inv H0.
    exists x0.
    replace (Sort s x0) with ((Sort s x0).[n/]) by autosubst.
    eapply substitutionN; eauto.
    rewrite <- H2.
    apply H1.
  - exists l; eauto.
Qed.

Theorem preservation Gamma m A s :
  [ Gamma |- ] ->
  [ Gamma |- m :- A -: s ] ->
  forall n, pstep m n -> 
    [ Gamma |- n :- A -: s ].
Proof.
  intros.
  dependent induction H0.
  - inv H1.
    apply p_axiom; eauto.
  - inv H1.
    apply s_axiom; eauto.
  - inv H1.
    assert ([A :u Gamma |-]).
    eapply u_ok; eauto.
    rewrite <-pure_re; eauto.
    specialize (IHhas_type1 H _ H7).
    specialize (IHhas_type2 H1 _ H8).
    eapply u_prop; eauto.
    eapply context_convU.
    eapply conv1i; eauto.
    rewrite <- pure_re; eauto.
    apply IHhas_type2.
  - inv H1.
    assert ([A :u Gamma |-]).
    eapply u_ok; eauto.
    rewrite <-pure_re; eauto.
    specialize (IHhas_type1 H _ H7).
    specialize (IHhas_type2 H1 _ H8).
    apply u_prod; eauto.
    eapply context_convU.
    eapply conv1i; eauto.
    rewrite <- pure_re; eauto.
    apply IHhas_type2.
  - inv H1.
    assert ([:n Gamma |-]).
    eapply n_ok; eauto.
    specialize (IHhas_type1 H _ H7).
    specialize (IHhas_type2 H1 _ H8).
    apply l_prod; eauto.
  - inv H1.
    apply u_var; eauto.
  - inv H1.
    apply l_var; eauto.
  - inv H1.
    pose proof (pure_re H0).
    pose proof H0_.
    rewrite H1 in H0_.
    destruct s.
    + apply u_prod_inv in H0_. first_order.
      assert ([A :u Gamma |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H6 _ H3).
      eapply u_lam; eauto.
    + apply l_prod_inv in H0_. first_order.
      assert ([A :l Gamma |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H6 _ H3).
      eapply u_lam; eauto.
  - inv H1.
    pose proof H0_.
    destruct s.
    + apply u_prod_inv in H0_. first_order.
      assert ([A :u Gamma |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H4 _ H2).
      eapply l_lam; eauto.
    + apply l_prod_inv in H0_. first_order.
      assert ([A :l Gamma |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H4 _ H2).
      eapply l_lam; eauto.
  - pose proof (merge_context_ok_inv H1 H). inv H3.
    inv H2.
    + specialize (IHhas_type1 H4 _ H7).
      specialize (IHhas_type2 H5 _ H9).
      pose proof (propagation H4 IHhas_type1). inv H2.
      apply u_prod_inv in H3. inv H3.
      pose proof (merge_re_re H1). first_order.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H11.
      assert ([re Gamma |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0).
      rewrite H12. rewrite H3. rewrite H6.
      apply merge_re_re_re.
      eapply conversion; eauto.
      eapply u_app; eauto.
    + assert (pstep (Lam m0) (Lam m')). 
      constructor; eauto.
      specialize (IHhas_type1 H4 _ H2).
      specialize (IHhas_type2 H5 _ H9).
      pose proof (propagation H4 IHhas_type1). inv H3.
      pose proof (u_prod_inv H6). first_order.
      pose proof (merge_re_re H1). inv H10.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H13.
      assert ([re Gamma |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0); eauto.
      rewrite H14. rewrite H11. rewrite H12.
      apply merge_re_re_re.
      eapply u_lam_inv in IHhas_type1; eauto.
      eapply conversion; eauto.
      eapply substitutionU; eauto.
  - pose proof (merge_context_ok_inv H0 H). inv H2.
    inv H1.
    + specialize (IHhas_type1 H3 _ H6).
      specialize (IHhas_type2 H4 _ H8).
      pose proof (propagation H3 IHhas_type1). inv H1.
      apply l_prod_inv in H2. inv H2.
      pose proof (merge_re_re H0). inv H2.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H9.
      assert ([re Gamma |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionN; eauto.
      rewrite <-H5.
      apply H1.
      eapply conversion; eauto.
      eapply l_app; eauto.
    + assert (pstep (Lam m0) (Lam m')). 
      constructor; eauto.
      specialize (IHhas_type1 H3 _ H1).
      specialize (IHhas_type2 H4 _ H8).
      pose proof (propagation H3 IHhas_type1). inv H2.
      pose proof (l_prod_inv H5). inv H2.
      pose proof (merge_re_re H0). inv H2.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H11.
      assert ([re Gamma |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionN; eauto.
      rewrite <- H9.
      apply H7.
      eapply l_lam_inv in IHhas_type1; eauto.
      eapply conversion; eauto.
      eapply substitutionL; eauto.
  - eapply conversion; eauto.
Qed.

Corollary preservation_step m n :
  step m n ->
  forall Gamma A s,
    [ Gamma |- ] ->
    [ Gamma |- m :- A -: s ] ->
    [ Gamma |- n :- A -: s ].
Proof.
  intros.
  eapply preservation; eauto.
  apply step_pstep; eauto.
Qed.

Corollary preservation_star_step m n :
  star step m n ->
  forall Gamma A s,
    [ Gamma |- ] ->
    [ Gamma |- m :- A -: s ] ->
    [ Gamma |- n :- A -: s ].
Proof.
  intro H.
  dependent induction H; intros; eauto.
  eapply preservation.
  apply H1.
  apply IHstar; eauto.
  apply step_pstep; eauto.
Qed.

Lemma canonical_tyProd m C :
  [ nil |- m :- C -: U ] -> value m ->
  forall A B s, 
    C <: TyProd A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma canonical_lnProd m C :
  [ nil |- m :- C -: L ] -> value m ->
  forall A B s, 
    C <: LnProd A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma canonical_arrow m C :
  [ nil |- m :- C -: U ] -> value m ->
  forall A B s, 
    C <: Arrow A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma canonical_lolli m C :
  [ nil |- m :- C -: L ] -> value m ->
  forall A B s, 
    C <: Lolli A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Theorem progress m A s :
  [ nil |- m :- A -: s ] -> value m \/ exists n, step m n.
Proof.
  intros.
  dependent induction H; try solve [left; constructor].
  - right.
    inv H2.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H2).
    specialize (IHhas_type2 H2).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_tyProd; eauto.
      destruct H5; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H4.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H3.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H3.
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
    inv H2.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H2).
    specialize (IHhas_type2 H2).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_lnProd; eauto.
      destruct H5; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H4.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H3.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H3.
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
  - apply IHhas_type2; eauto.
Qed.

Inductive isL : context term -> nat -> Prop :=
| isL_O Gamma A :
  isL (A :l Gamma) 0
| isL_S Gamma i A s :
  isL Gamma i ->
  isL (A :[s] Gamma) (i.+1)
| isL_N Gamma i :
  isL Gamma i ->
  isL (:n Gamma) (i.+1).

Inductive isN : context term -> nat -> Prop :=
| isN_O Gamma :
  isN (:n Gamma) 0
| isN_S Gamma i A s :
  isN Gamma i ->
  isN (A :[s] Gamma) (i.+1)
| isN_N Gamma i :
  isN Gamma i ->
  isN (:n Gamma) (i.+1).

Fixpoint occurs (i : nat) (m : term) : nat :=
  match m with
  | Var x => if x == i then 1 else 0
  | Sort _ _ => 0
  | TyProd A B _ => occurs i A + occurs (i.+1) B
  | LnProd A B _ => occurs i A + occurs (i.+1) B
  | Arrow A B _ => occurs i A + occurs i B
  | Lolli A B _ => occurs i A + occurs i B
  | Lam m => occurs (i.+1) m
  | App m n => occurs i m + occurs i n
  end.

Lemma eqn_refl (n : nat) : n == n.
Proof.
  induction n; simpl; eauto.
Qed.

Lemma isL_pure Gamma i : isL Gamma i -> ~pure Gamma.
Proof.
  induction 1; unfold not; intros.
  inv H.
  destruct s.
  inv H0. firstorder.
  inv H0.
  inv H0. firstorder.
Qed.

Lemma isL_hasU Gamma i : 
  isL Gamma i -> forall x A, ~hasU Gamma x A.
Proof.
  induction 1; intros; unfold not; intros.
  inv H.
  destruct s.
  inv H0. exfalso. eapply isL_pure; eauto.
  firstorder.
  inv H0.
  inv H0.
  firstorder.
Qed.

Lemma isL_hasL Gamma i :
  isL Gamma i -> forall x A, hasL Gamma x A -> x = i.
Proof.
  induction 1; intros.
  inv H; eauto.
  destruct s.
  inv H0.
  pose proof (IHisL _ _ H5); eauto.
  inv H0; eauto.
  exfalso. eapply isL_pure; eauto.
  inv H0.
  pose proof (IHisL _ _ H2); eauto.
Qed.

Lemma isN_hasU Gamma i :
  isN Gamma i -> forall x A, hasU Gamma x A -> x == i = false.
Proof.
  induction 1; intros; eauto.
  inv H; eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H6); eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H2); eauto.
Qed.

Lemma isN_hasL Gamma i :
  isN Gamma i -> forall x A, hasL Gamma x A -> x == i = false.
Proof.
  induction 1; intros; eauto.
  inv H; eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H6); eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H2); eauto.
Qed.

Lemma isL_merge_inv Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma -> 
    forall i, isL Gamma i -> 
      (isL Gamma1 i /\ isN Gamma2 i) \/
      (isL Gamma2 i /\ isN Gamma1 i).
Proof.
  intro H.
  dependent induction H; intros.
  - inv H.
  - inv H0.
    apply IHmerge in H5.
    firstorder.
    + left; repeat constructor; eauto.
    + right; repeat constructor; eauto.
  - inv H0.
    + left; repeat constructor; eauto.
    + apply IHmerge in H5.
      inv H5.
      * left; inv H0; repeat constructor; eauto.
      * right; inv H0; repeat constructor; eauto.
  - inv H0.
    + right; repeat constructor; eauto.
    + apply IHmerge in H5.
      firstorder.
      * left; repeat constructor; eauto.
      * right; repeat constructor; eauto.
  - inv H0.
    apply IHmerge in H2.
    firstorder.
    + left; repeat constructor; eauto.
    + right; repeat constructor; eauto.
Qed.

Lemma isN_merge_inv Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma -> 
    forall i, isN Gamma i -> 
      isN Gamma1 i /\ isN Gamma2 i.
Proof.
  intro H.
  dependent induction H; intros.
  - inv H.
  - inv H0.
    apply IHmerge in H5.
    firstorder; constructor; eauto.
  - inv H0.
    apply IHmerge in H5.
    firstorder; constructor; eauto.
  - inv H0.
    apply IHmerge in H5.
    firstorder; constructor; eauto.
  - inv H0; firstorder; constructor; firstorder.
Qed.

Lemma narity Gamma m A s :
  [ Gamma |- m :- A -: s ] -> 
    forall i, isN Gamma i -> occurs i m = 0.
Proof.
  intro H.
  dependent induction H; simpl; intros.
  - eauto.
  - eauto.
  - rewrite IHhas_type1; eauto.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - rewrite IHhas_type1; eauto.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - rewrite IHhas_type1; eauto.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - rewrite IHhas_type1; eauto.
  - rewrite IHhas_type1; eauto.
  - pose proof (isN_hasU H0 H).
    rewrite H1; eauto.
  - pose proof (isN_hasL H0 H).
    rewrite H1; eauto.
  - apply IHhas_type2.
    constructor; eauto.
  - apply IHhas_type2.
    constructor; eauto.
  - apply IHhas_type2.
    constructor; eauto.
  - apply IHhas_type2.
    constructor; eauto.
  - pose proof (isN_merge_inv H2 H3). inv H4.
    rewrite IHhas_type1; eauto.
  - pose proof (isN_merge_inv H1 H2). inv H3.
    rewrite IHhas_type1; eauto.
  - pose proof (isN_merge_inv H2 H3). inv H4.
    rewrite IHhas_type1; eauto.
  - pose proof (isN_merge_inv H1 H2). inv H3.
    rewrite IHhas_type1; eauto.
  - apply IHhas_type2; eauto.
Qed.

Theorem linearity Gamma m A s :
  [ Gamma |- m :- A -: s ] -> 
    forall i, isL Gamma i -> occurs i m = 1.
Proof.
  intro H.
  dependent induction H; intros.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_hasU; eauto.
  - pose proof (isL_hasL H0 H).
    rewrite H1; simpl.
    rewrite eqn_refl; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - simpl.
    apply IHhas_type2.
    constructor; eauto.
  - simpl.
    apply IHhas_type2.
    constructor; eauto.
  - pose proof (isL_merge_inv H2 H3).
    firstorder; simpl.
    + apply IHhas_type1 in H4.
      eapply narity in H5; eauto.
      rewrite H4.
      rewrite H5.
      eauto.
    + apply IHhas_type2 in H4.
      eapply narity in H5; eauto.
      rewrite H4.
      rewrite H5.
      eauto.
  - pose proof (isL_merge_inv H1 H2).
    firstorder; simpl.
    + apply IHhas_type1 in H3.
      eapply narity in H4; eauto.
      rewrite H3.
      rewrite H4.
      eauto.
    + apply IHhas_type2 in H3.
      eapply narity in H4; eauto.
      rewrite H3.
      rewrite H4.
      eauto.
  - pose proof (isL_merge_inv H2 H3).
    firstorder; simpl.
    + apply IHhas_type1 in H4.
      eapply narity in H5; eauto.
      rewrite H4.
      rewrite H5.
      eauto.
    + apply IHhas_type2 in H4.
      eapply narity in H5; eauto.
      rewrite H4.
      rewrite H5.
      eauto.
  - pose proof (isL_merge_inv H1 H2).
    firstorder; simpl.
    + apply IHhas_type1 in H3.
      eapply narity in H4; eauto.
      rewrite H3.
      rewrite H4.
      eauto.
    + apply IHhas_type2 in H3.
      eapply narity in H4; eauto.
      rewrite H3.
      rewrite H4.
      eauto.
  - apply IHhas_type2; eauto.
Qed.

Close Scope clc_scope.

Import CC.

Fixpoint erase (m : CLC.term) : CC.term :=
  match m with
  | CLC.Var x => CC.Var x
  | CLC.Sort _ l => CC.Sort l
  | CLC.TyProd A B _ => CC.Prod (erase A) (erase B)
  | CLC.LnProd A B _ => CC.Prod (erase A) (erase B)
  | CLC.Arrow A B _ => CC.Prod (erase A) (erase B).[ren (+1)]
  | CLC.Lolli A B _ => CC.Prod (erase A) (erase B).[ren (+1)]
  | CLC.Lam n => CC.Lam (erase n)
  | CLC.App m n => CC.App (erase m) (erase n)
  end.

Fixpoint erase_context 
  (Gamma : CLC.context CLC.term) 
: CC.context CC.term :=
  match Gamma with
  | Some (t, U) :: Gamma => erase t :s erase_context Gamma
  | Some (t, L) :: Gamma => erase t :s erase_context Gamma
  | None :: Gamma => :n erase_context Gamma
  | nil => nil
  end.

Notation "[| m |]" := (erase m).
Notation "[[ Gamma ]]" := (erase_context Gamma).

Lemma erase_value v : 
  CLC.value v <-> CC.value [|v|].
Proof.
  split.
  induction 1; simpl; constructor.
  induction v; simpl; try constructor.
  intros.
  inv H.
Qed.

Definition erase_subst 
  (sigma : var -> CLC.term) 
  (tau : var -> CC.term)
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
  CLC.pstep m n -> CC.pstep [|m|] [|n|].
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
  conv CLC.pstep m n -> conv CC.pstep [|m|] [|n|].
Proof.
  induction 1; eauto.
  eapply conv_trans.
  apply IHconv.
  eapply convSE; eauto.
  apply erase_pstep; eauto.
  eapply convSEi; eauto.
  apply erase_pstep; eauto.
Qed.

Lemma erase_sub1 m n :
  CLC.sub1 m n -> CC.sub1 [|m|] [|n|].
Proof.
  induction 1; asimpl; eauto using sub1.
  constructor.
  apply sub1_subst; eauto.
  constructor.
  apply sub1_subst; eauto.
Qed.

Lemma erase_sub m n :
  CLC.sub m n -> CC.sub [|m|] [|n|].
Proof.
  move=> [A B sb] c1 c2.
  inv sb.
  - assert (conv CLC.pstep m n).
    eapply conv_trans.
    apply c1.
    apply c2.
    apply erase_conv in H.
    apply conv_sub; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    assert (sub1 (prop) (@l)).
    constructor; eauto.
    apply sub1_sub in H.
    eapply sub_trans. eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    assert (sub1 (@l1) (@l2)).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert (sub1 (Prod [|A0|] [|B1|]) (Prod [|A0|] [|B2|])).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert (sub1 (Prod [|A0|] [|B1|]) (Prod [|A0|] [|B2|])).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert 
      (sub1 (Prod [|A0|] [|B1|].[ren (+1)]) 
            (Prod [|A0|] [|B2|].[ren (+1)])).
    constructor; eauto.
    apply sub1_subst; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert 
      (sub1 (Prod [|A0|] [|B1|].[ren (+1)]) 
            (Prod [|A0|] [|B2|].[ren (+1)])).
    constructor; eauto.
    apply sub1_subst; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma hasU_erase Gamma x A :
  hasU Gamma x A -> has [[ Gamma ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
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

Inductive agree_wk : 
  CC.context CC.term -> CC.context CC.term -> Prop :=
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
  - destruct a. 
    destruct p.
    destruct s; simpl; constructor; eauto.
    constructor; eauto.
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
  - apply p_axiom.
  - apply t_axiom.
  - eapply ty_prop; eauto.
    apply IHhas_type2; constructor; eauto.
  - apply ty_prod.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - pose proof (agree_wk_has H0 H).
    apply ty_var; eauto.
  - eapply ty_lam.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_app.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
  - eapply ty_conv.
    apply H.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma erase_re Gamma m A :
  [ [[re Gamma]] |- m :- A ] ->
  [ [[Gamma]] |- m :- A ].
Proof.
  intro H.
  eapply wk_ok; eauto.
  apply agree_wk_re.
Qed.

Lemma erase_subst_trivial n :
  erase_subst (n .: ids) ([|n|] .: ids).
Proof.
  unfold erase_subst; intros.
  destruct x; simpl; eauto.
Qed.

Theorem embedding Gamma m A s : 
  [ Gamma |- m :- A -: s ] ->
  [ [[ Gamma ]] |- [| m |] :- [| A |] ].
Proof.
  intro H.
  dependent induction H; asimpl.
  - apply p_axiom.  
  - apply t_axiom.  
  - eapply ty_prop; eauto.
  - apply ty_prod; eauto.
  - apply ty_prod; eauto.
  - apply ty_prod; eauto.
    replace (@l) with ((@l).[ren (+1)]) by autosubst.
    apply weakening; eauto.
  - apply ty_prod; eauto.
    replace (@l) with ((@l).[ren (+1)]) by autosubst.
    apply weakening; eauto.
  - apply hasU_erase in H.
    apply ty_var; eauto.
  - apply hasL_erase in H.
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
    apply agree_wk_merge_inv in H2; destruct H2.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H1; destruct H1.
    replace [|B|] with ([|B|].[ren (+1)].[[|n|]/]) by autosubst.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H2; destruct H2.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H1; destruct H1.
    replace [|B|] with ([|B|].[ren (+1)].[[|n|]/]) by autosubst.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - eapply ty_conv.
    apply erase_sub; eauto.
    simpl in IHhas_type1.
    eapply wk_ok; eauto.
    apply agree_wk_re.
    apply IHhas_type2.
Qed.

Corollary embedding_context Gamma :
  CLC.context_ok Gamma -> [ [[Gamma]] |- ].
Proof.
  induction 1; simpl. 
  constructor.
  apply embedding in H0.
  apply erase_re in H0.
  econstructor; eauto.
  apply embedding in H0.
  apply erase_re in H0.
  econstructor; eauto.
  constructor; eauto.
Qed.

End CLC.
