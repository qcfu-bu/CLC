From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program.
Require Import AutosubstSsr ARS Context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sort : Type := U | L.

Inductive term : Type :=
| Var    (x : var)
| Sort   (srt : sort)
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
| value_sort srt     : value (Sort srt)
| value_var x        : value (Var x)
| value_tyProd A B s : value (TyProd A B s)
| value_lnProd A B s : value (LnProd A B s)
| value_arrow A B s  : value (Arrow A B s)
| value_lolli A B s  : value (Lolli A B s)
| value_lam n        : value (Lam n).

Definition v_subst (sigma : var -> term) : Prop := 
  forall x, value (sigma x).

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
| pstep_sort srt :
  pstep (Sort srt) (Sort srt)
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
  - inv H0. exists (Sort srt)...
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

Lemma value_rename xi A :
  value A -> value A.[ren xi].
Proof.
  intros.
  apply value_subst; eauto.
  apply rename_v_subst.
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
  [ A :L Gamma |- B :- Sort s -: U ] ->
  [ Gamma |- TyProd A B s :- Sort U -: U ]
| l_prod Gamma A B s :
  pure Gamma ->
  [ Gamma |- A :- Sort U -: U ] ->
  [ A :L Gamma |- B :- Sort s -: U ] ->
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
  hasL Gamma x A ->
  [ Gamma |- Var x :- A -: U ]
| l_var Gamma x A :
  hasR Gamma x A ->
  [ Gamma |- Var x :- A -: L ]
| u_lam1 Gamma n A B s :
  pure Gamma ->
  [ Gamma |- TyProd A B s :- Sort U -: U ] ->
  [ A :L Gamma |- n :- B -: s ] ->
  [ Gamma |- Lam n :- TyProd A B s -: U ]
| u_lam2 Gamma n A B s :
  pure Gamma ->
  [ Gamma |- Arrow A B s :- Sort U -: U ] ->
  [ A :R Gamma |- n :- B.[ren (+1)] -: s ] ->
  [ Gamma |- Lam n :- Arrow A B s -: U ]
| l_lam1 Gamma n A B s :
  [ re Gamma |- LnProd A B s :- Sort L -: U ] ->
  [ A :L Gamma |- n :- B -: s ] ->
  [ Gamma |- Lam n :- LnProd A B s -: L ]
| l_lam2 Gamma n A B s :
  [ re Gamma |- Lolli A B s :- Sort L -: U ] ->
  [ A :R Gamma |- n :- B.[ren (+1)] -: s ] ->
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
  [ re Gamma |- A :- Sort s -: U ] ->
  [ re Gamma |- B :- Sort s -: U ] ->
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
  [ A :L Gamma |- ]
| l_ok Gamma A :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort L -: U ] ->
  [ A :R Gamma |- ]
| n_ok Gamma :
  [ Gamma |- ] ->
  [ :N Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Lemma re_ok Gamma :
  [ Gamma |- ] ->
  [ re Gamma |- ].
Proof with eauto using context_ok.
  intros.
  induction H...
  - simpl.
    apply u_ok...
    rewrite <- re_re.
    assumption.
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
    eapply agree_ren_hasL; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply l_var.
    eapply agree_ren_hasR; eauto.
  - apply u_lam1.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    asimpl.
    apply IHhas_type2; eauto.
    constructor; eauto.
  - asimpl.
    apply u_lam2.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    replace (B.[ren xi].[ren (+1)]) 
      with (B.[ren (+1)].[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - apply l_lam1.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    asimpl.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    apply l_lam2.
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
  - pose proof (agree_ren_re_re H3).
    pose proof (IHhas_type1 _ _ H4). asimpl in H5.
    pose proof (IHhas_type2 _ _ H4). asimpl in H6.
    eapply conversion.
    apply H5.
    apply H6.
    apply rename_subst; eauto.
    apply IHhas_type3; eauto.
Qed.

Lemma hasL_ok Gamma :
  [ Gamma |- ] ->
  forall x A,
    hasL Gamma x A ->
    [ re Gamma |- A :- Sort U -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    replace (Sort U) with ((Sort U).[ren (+1)]) by autosubst.
    eapply rename_ok.
    apply H0.
    apply agree_ren_wkL.
    rewrite <- pure_re; eauto.
    apply agree_ren_refl.
    replace (Sort U) with ((Sort U).[ren (+1)]) by autosubst.
    first_order.
    eapply rename_ok.
    apply IHcontext_ok.
    apply agree_ren_wkL.
    apply agree_ren_refl.
  - inv H1.
  - inv H0.
    replace (Sort U) with ((Sort U).[ren (+1)]) by autosubst.
    first_order.
    eapply rename_ok.
    apply IHcontext_ok.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma hasR_ok Gamma :
  [ Gamma |- ] ->
  forall x A,
    hasR Gamma x A ->
    [ re Gamma |- A :- Sort L -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    replace (Sort L) with ((Sort L).[ren (+1)]) by autosubst.
    first_order.
    eapply rename_ok.
    apply IHcontext_ok.
    apply agree_ren_wkL.
    apply agree_ren_refl.
  - inv H1; simpl.
    replace (Sort L) with ((Sort L).[ren (+1)]) by autosubst.
    eapply rename_ok.
    apply H0.
    apply agree_ren_wkN.
    apply agree_ren_refl.
  - inv H0; simpl.
    replace (Sort L) with ((Sort L).[ren (+1)]) by autosubst.
    first_order.
    eapply rename_ok.
    apply IHcontext_ok.
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
  [ Gamma |- ] ->
  [ Gamma |- m :- A -: U ] -> 
  value m -> pure Gamma.
Proof.
  intros H H1.
  dependent induction H1; intros; eauto.
  - eapply hasL_pure; eauto.
  - inv H1.
  - inv H1.
  - inv H1.
  - inv H1.
Qed.

Lemma weakening_L Gamma m A s B :
  [ Gamma |- m :- A -: s ] ->
  [ B :L Gamma |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkL.
  apply agree_ren_refl.
Qed.

Lemma weakening_N Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  [ :N Gamma |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
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
  [ Gamma |- m :- A -: s ] -> 
  [ B :L Gamma |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakening_L; eauto.
Qed.

Lemma eweakening_N Gamma m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A -: s ] -> 
  [ :N Gamma |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakening_N; eauto.
Qed.

Reserved Notation "[ Delta |- sigma -| Gamma ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil sigma :
  [ nil |- sigma -| nil ]
| agree_subst_L Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] :L Delta |- up sigma -| A :L Gamma ]
| agree_subst_R Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] :R Delta |- up sigma -| A :R Gamma ]
| agree_subst_N Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ :N Delta |- up sigma -| :N Gamma ]
| agree_subst_wkL Delta sigma Gamma n A :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- n :- A.[sigma] -: U ] ->
  [ Delta |- n .: sigma -| A :L Gamma ]
| agree_subst_wkN Delta sigma Gamma n :
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- n .: sigma -| :N Gamma ]
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
  inv H0; eauto.
Qed.

Lemma agree_subst_refl Gamma :
  [ Gamma |- ids -| Gamma ].
Proof.
  induction Gamma.
  - constructor.
  - destruct a.
    replace ([Left t :: Gamma |- ids -| Left t :: Gamma])
      with ([Left t.[ids] :: Gamma |- up ids -| Left t :: Gamma])
      by autosubst.
    apply agree_subst_L; eauto.
    replace ([Right t :: Gamma |- ids -| Right t :: Gamma])
      with ([Right t.[ids] :: Gamma |- up ids -| Right t :: Gamma])
      by autosubst.
    apply agree_subst_R; eauto.
    replace (ids) with (up ids) by autosubst.
    apply agree_subst_N; eauto.
Qed.

Lemma agree_subst_hasL Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  forall x A,
    hasL Gamma x A -> 
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
    + eapply eweakening_L; eauto.
      autosubst.
      autosubst.
  - inv H0.
  - inv H0.
    eapply eweakening_N; eauto.
    autosubst.
    autosubst.
  - inv H1; asimpl; eauto.
    pose proof (agree_subst_pure H H6).
    pose proof (pure_re H1).
    rewrite H2; eauto.
  - inv H0; asimpl; eauto.
Qed.

Lemma agree_subst_hasR Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  forall x A,
    hasR Gamma x A -> 
    [ Delta |- sigma x :- A.[sigma] -: L ].
Proof.
  induction 1; intros.
  - inv H.
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
  - inv H1; asimpl; eauto.
  - inv H0; asimpl; eauto.
Qed.

Lemma agree_subst_re_re Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- sigma -| re Gamma ].
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
    rewrite <- re_re; eauto.
  - constructor; eauto.
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
    repeat constructor.
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
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists x.
    exists x0.
    repeat constructor; eauto.
Qed.

Lemma substitution Gamma m A s :
  [ Gamma |- m :- A -: s ] ->
  forall Delta sigma,
    v_subst sigma ->
    [ Delta |- sigma -| Gamma ] ->
    [ Delta |- m.[sigma] :- A.[sigma] -: s ].
Proof.
  intros H.
  dependent induction H; asimpl; intros; eauto.
  - apply axiom.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2 H3). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H3).
    pose proof (v_subst_up H2).
    specialize (IHhas_type2 _ _ H5 H4). asimpl in IHhas_type2.
    apply u_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2 H3). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H3).
    pose proof (v_subst_up H2).
    specialize (IHhas_type2 _ _ H5 H4). asimpl in IHhas_type2.
    apply l_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2 H3). asimpl in IHhas_type1.
    specialize (IHhas_type2 _ _ H2 H3). asimpl in IHhas_type2.
    apply arrow; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2 H3). asimpl in IHhas_type1.
    specialize (IHhas_type2 _ _ H2 H3). asimpl in IHhas_type2.
    apply lolli; eauto.
    eapply agree_subst_pure; eauto.
  - eapply agree_subst_hasL; eauto.
  - eapply agree_subst_hasR; eauto.
  - specialize (IHhas_type1 _ _ H2 H3). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H3).
    pose proof (v_subst_up H2).
    specialize (IHhas_type2 _ _ H5 H4).
    apply u_lam1; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2 H3). asimpl in IHhas_type1.
    pose proof (agree_subst_R A H3).
    pose proof (v_subst_up H2).
    specialize (IHhas_type2 _ _ H5 H4). asimpl in IHhas_type2.
    apply u_lam2; eauto.
    eapply agree_subst_pure; eauto.
    asimpl; eauto.
  - pose proof (agree_subst_re_re H2).
    specialize (IHhas_type1 _ _ H1 H3). asimpl in IHhas_type1.
    pose proof (agree_subst_L A H2).
    pose proof (v_subst_up H1).
    specialize (IHhas_type2 _ _ H5 H4).
    apply l_lam1; eauto.
  - pose proof (agree_subst_re_re H2).
    specialize (IHhas_type1 _ _ H1 H3). asimpl in IHhas_type1.
    pose proof (agree_subst_R A H2).
    pose proof (v_subst_up H1).
    specialize (IHhas_type2 _ _ H5 H4). asimpl in IHhas_type2.
    apply l_lam2; eauto.
    asimpl; eauto.
  - pose proof (merge_agree_subst_inv H3 H1).
    first_order.
    eapply u_app1; eauto.
  - pose proof (merge_agree_subst_inv H3 H1).
    first_order.
    eapply u_app2; eauto.
  - pose proof (merge_agree_subst_inv H3 H1).
    first_order.
    eapply l_app1; eauto.
  - pose proof (merge_agree_subst_inv H3 H1).
    first_order.
    eapply l_app2; eauto.
  - eapply conversion.
    apply IHhas_type1.
    apply H3.
    apply agree_subst_re_re; eauto.
    apply IHhas_type2; eauto.
    apply agree_subst_re_re; eauto.
    apply conv_subst; eauto.
    apply IHhas_type3; eauto.
Qed.

Lemma substitutionL Gamma1 m A B s :
  [ Gamma1 |- ] ->
  [ A :L Gamma1 |- m :- B -: s ] ->
  forall Gamma2 Gamma n,
    value n ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |- ] ->
    [ Gamma2 |- n :- A -: U ] -> 
    [ Gamma |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H0.
  apply value_v_subst; eauto.
  pose proof (value_sound H3 H4 H1).
  pose proof (merge_pure2 H2 H5).
  rewrite H6.
  apply agree_subst_wkL.
  apply agree_subst_refl.
  pose proof (merge_re_re H2).
  destruct H7.
  asimpl.
  rewrite H7.
  rewrite <- H8.
  rewrite <- pure_re; eauto.
Qed.

Lemma substitutionN Gamma1 m A B s :
  [ Gamma1 |- ] ->
  [ :N Gamma1 |- m :- B -: s ] ->
  forall Gamma2 n t,
    value n ->
    [ Gamma2 |- ] ->
    [ Gamma2 |- n :- A -: t ] -> 
    [ Gamma1 |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H0.
  apply value_v_subst; eauto.
  apply agree_subst_wkN.
  apply agree_subst_refl.
Qed.

Lemma substitutionR Gamma1 m A B s :
  [ A :R Gamma1 |- m :- B -: s ] ->
  forall Gamma2 Gamma n,
    value n ->
    merge Gamma1 Gamma2 Gamma -> 
    [ Gamma2 |- n :- A -: L ] -> 
    [ Gamma |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros H.
  dependent induction H; intros.
  - inv H.
  - inv H.
  - inv H.
  - inv H.
  - inv H.
  - inv H.
  - inv H.
    asimpl.
    pose proof (merge_pure1 H1 H7).
    rewrite H; eauto.
  - inv H.
  - inv H.
  - admit.
  - admit.
  - inv H1.
    assert (A :R Gamma4 = A :R Gamma4) by eauto.
    pose proof (IHhas_type1 Gamma4 A H1 Gamma5 Gamma1 n0 H2 H8).
    asimpl.
    eapply u_app1.
    asimpl in H5.
    apply H5.
    