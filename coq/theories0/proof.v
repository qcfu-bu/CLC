From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var (x : var)
| U
| L
| TyProd (A : term) (B : {bind term})
| LnProd (A : term) (B : {bind term})
| Arrow  (A B : term)
| Lolli  (A B : term)
| TyLam  (n : {bind term})
| LnLam  (n : {bind term})
| App    (m n : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_U : value U
| value_L : value L
| value_var x : value (Var x)
| value_tyProd A B : value (TyProd A B)
| value_lnProd A B : value (LnProd A B)
| value_arrow  A B : value (Arrow A B)
| value_lolli  A B : value (Lolli A B)
| value_tyLam  n   : value (TyLam n)
| value_lnLam  n   : value (LnLam n).

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
| step_tyBeta n v :
  value v ->
  step (App (TyLam n) v) (n.[v/])
| step_lnBeta n v :
  value v ->
  step (App (LnLam n) v) (n.[v/])
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
| pstep_U :
  pstep U U
| pstep_L :
  pstep L L
| pstep_tyLam n n' : 
  pstep n n' -> 
  pstep (TyLam n) (TyLam n')
| pstep_lnLam n n' : 
  pstep n n' -> 
  pstep (LnLam n) (LnLam n')
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_tyBeta n n' v v' :
  pstep n n' ->
  value v ->
  pstep v v' ->
  pstep (App (TyLam n) v) (n'.[v'/])
| pstep_lnBeta n n' v v' :
  pstep n n' ->
  value v ->
  pstep v v' ->
  pstep (App (LnLam n) v) (n'.[v'/])
| pstep_tyProd A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (TyProd A B) (TyProd A' B')
| pstep_lnProd A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (LnProd A B) (LnProd A' B')
| pstep_arrow A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Arrow A B) (Arrow A' B')
| pstep_lolli A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Lolli A B) (Lolli A' B').

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
  inv H2.
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
    apply pstep_tyLam.
    apply IHpstep.
    apply v_subst_up...
  - asimpl. 
    apply pstep_lnLam.
    apply IHpstep.
    apply v_subst_up...
  - asimpl.
    pose proof (v_subst_up H2).
    specialize (IHpstep1 _ H3).
    specialize (IHpstep2 _ H2).
    pose proof (value_subst H0 H2).
    pose proof (pstep_tyBeta IHpstep1 H4 IHpstep2).
    asimpl in H5...
  - asimpl.
    pose proof (v_subst_up H2).
    specialize (IHpstep1 _ H3).
    specialize (IHpstep2 _ H2).
    pose proof (value_subst H0 H2).
    pose proof (pstep_lnBeta IHpstep1 H4 IHpstep2).
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
    pose proof (pstep_tyBeta H6 H9 H7).
    asimpl in H10...
  - pose proof (v_subst_up H2).
    pose proof (psstep_up H3).
    pose proof (IHpstep1 _ _ H4 H5).
    pose proof (IHpstep2 _ _ H2 H3).
    pose proof (psstep_v_subst H3 H2).
    pose proof (value_subst H0 H2).
    pose proof (pstep_lnBeta H6 H9 H7).
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

Lemma pstep_diamond m m1 :
  pstep m m1 ->
    forall m2, pstep m m2 ->
      exists m', pstep m1 m' /\ pstep m2 m'.
Proof with eauto using pstep.
  intros.
  dependent induction H.
  - inv H0. exists (Var x)...
  - inv H0. exists (U)...
  - inv H0. exists (L)...
  - inv H0.  apply (IHpstep) in H2. firstorder. exists (TyLam x)...
  - inv H0.  apply (IHpstep) in H2. firstorder. exists (LnLam x)...
  - inv H1.
    + apply (IHpstep1) in H4. apply (IHpstep2) in H6. firstorder.
      exists (App x0 x)...
    + inv H. 
      assert (pstep (TyLam n0) (TyLam n'0))...
      pose proof (pstep_value H7 H5). 
      pose proof (pstep_value H0 H5).
      apply (IHpstep1) in H. apply (IHpstep2) in H7. firstorder.
      inv H.
      inv H6.
      exists (n'2.[x0/]). split.
      apply pstep_tyBeta...
      apply pstep_compat_beta...
    + inv H. 
      assert (pstep (LnLam n0) (LnLam n'0))...
      pose proof (pstep_value H7 H5). 
      pose proof (pstep_value H0 H5).
      apply (IHpstep1) in H. apply (IHpstep2) in H7. firstorder.
      inv H.
      inv H6.
      exists (n'2.[x0/]). split.
      apply pstep_lnBeta...
      apply pstep_compat_beta...
  - inv H2.
    + inv H5.
      pose proof (pstep_value H7 H0).
      apply IHpstep2 in H7. apply IHpstep1 in H3. firstorder.
      exists (x.[x0/]). split.
      * apply pstep_compat_beta...
        eapply pstep_value; eauto.
      * apply pstep_tyBeta...
    + pose proof (pstep_value H8 H0).
      apply IHpstep1 in H5. apply IHpstep2 in H8. firstorder.
      exists (x0.[x/]). split.
      * apply pstep_compat_beta...
        eapply pstep_value; eauto.
      * apply pstep_compat_beta...
  - inv H2.
    + inv H5.
      pose proof (pstep_value H7 H0).
      apply IHpstep2 in H7. apply IHpstep1 in H3. firstorder.
      exists (x.[x0/]). split.
      * apply pstep_compat_beta...
        eapply pstep_value; eauto.
      * apply pstep_lnBeta...
    + pose proof (pstep_value H8 H0).
      apply IHpstep1 in H5. apply IHpstep2 in H8. firstorder.
      exists (x0.[x/]). split.
      * apply pstep_compat_beta...
        eapply pstep_value; eauto.
      * apply pstep_compat_beta...
  - inv H1. apply (IHpstep1) in H4. apply (IHpstep2) in H6.
    firstorder. exists (TyProd x0 x)...
  - inv H1. apply (IHpstep1) in H4. apply (IHpstep2) in H6.
    firstorder. exists (LnProd x0 x)...
  - inv H1. apply (IHpstep1) in H4. apply (IHpstep2) in H6.
    firstorder. exists (Arrow x0 x)...
  - inv H1. apply (IHpstep1) in H4. apply (IHpstep2) in H6.
    firstorder. exists (Lolli x0 x)...
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> red m m2 ->
    exists m', red m1 m' /\ pstep m2 m'.
Proof with eauto using pstep_refl, star.
  intros.
  dependent induction H0... firstorder.
  pose proof (pstep_diamond H1 H3). firstorder.
  exists x0. split...
Qed.

Theorem confluence m m1 m2 :
  red m m1 -> red m m2 -> 
    exists m', red m1 m' /\ red m2 m'.
Proof with eauto using pstep_refl, star.
  intros.
  dependent induction H.
  - exists m2. split...
  - firstorder.
    pose proof (strip H0 H2). firstorder.
    exists x0. split...
Qed.
Hint Resolve confluence.

Notation "Gamma `_ i" := (dget Gamma i) (at level 2).

Reserved Notation "[ Gamma ; Delta |- ]".
Reserved Notation "[ Gamma ; Delta |- s :- A ]".
  
Inductive has_type : seq_opt term -> seq_opt term -> term -> term -> Prop :=
| u_axiom Gamma Delta : 
  [ Gamma ; pure Delta |- U :- U ]
| l_axiom Gamma Delta :
  [ Gamma ; pure Delta |- L :- U ]
| u_prod1 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- U ] ->
  [ A ::: Gamma ; None :: pure Delta |- B :- U ] ->
  [ Gamma ; pure Delta |- TyProd A B :- U ]
| u_prod2 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- U ] ->
  [ A ::: Gamma ; None :: pure Delta |- B :- L ] ->
  [ Gamma ; pure Delta |- TyProd A B :- U ]
| l_prod1 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- U ] ->
  [ A ::: Gamma ; None :: pure Delta |- B :- U ] ->
  [ Gamma ; pure Delta |- LnProd A B :- L ]
| l_prod2 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- U ] ->
  [ A ::: Gamma ; None :: pure Delta |- B :- L ] ->
  [ Gamma ; pure Delta |- LnProd A B :- L ]
| arrow1 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- L ] ->
  [ Gamma ; pure Delta |- B :- U ] ->
  [ Gamma ; pure Delta |- Arrow A B :- U ]
| arrow2 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- L ] ->
  [ Gamma ; pure Delta |- B :- L ] ->
  [ Gamma ; pure Delta |- Arrow A B :- U ]
| lolli1 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- L ] ->
  [ Gamma ; pure Delta |- B :- U ] ->
  [ Gamma ; pure Delta |- Lolli A B :- L ]
| lolli2 Gamma Delta A B :
  [ Gamma ; pure Delta |- A :- L ] ->
  [ Gamma ; pure Delta |- B :- L ] ->
  [ Gamma ; pure Delta |- Lolli A B :- L ]
| u_var Gamma Delta x A : 
  has Gamma x A ->
  [ Gamma ; pure Delta |- Var x :- A ]
| l_var Gamma Delta x A :
  only Delta x A ->
  [ Gamma ; Delta |- Var x :- A ]
| u_lam1 Gamma Delta n A B :
  [ Gamma ; pure Delta |- TyProd A B :- U ] ->
  [ A ::: Gamma ; None :: pure Delta |- n :- B ] ->
  [ Gamma ; pure Delta |- TyLam n :- TyProd A B ]
| u_lam2 Gamma Delta n A B :
  [ Gamma ; pure Delta |- Arrow A B :- U ] ->
  [ None :: Gamma ; A ::: pure Delta |- n :- B.[ren (+1)] ] ->
  [ Gamma ; pure Delta |- TyLam n :- Arrow A B ]
| l_lam1 Gamma Delta n A B :
  [ Gamma ; pure Delta |- LnProd A B :- L ] ->
  [ A ::: Gamma ; None :: Delta |- n :- B ] ->
  [ Gamma ; Delta |- LnLam n :- LnProd A B ]
| l_lam2 Gamma Delta n A B :
  [ Gamma ; pure Delta |- Lolli A B :- L ] ->
  [ None :: Gamma ; A ::: Delta |- n :- B.[ren (+1)] ] ->
  [ Gamma ; Delta |- LnLam n :- Lolli A B ]
| u_app1 Gamma Delta1 Delta2 Delta A B m n :
  [ Gamma ; Delta1 |- m :- TyProd A B ] ->
  [ Gamma ; Delta2 |- n :- A ] ->
  merge Delta1 Delta2 Delta ->
  [ Gamma ; Delta |- App m n :- App (TyLam B) n ]
| u_app2 Gamma Delta1 Delta2 Delta A B m n :
  [ Gamma ; Delta1 |- m :- Arrow A B ] ->
  [ Gamma ; Delta2 |- n :- A ] ->
  merge Delta1 Delta2 Delta ->
  [ Gamma ; Delta |- App m n :- B ]
| l_app1 Gamma Delta1 Delta2 Delta A B m n :
  [ Gamma ; Delta1 |- m :- LnProd A B ] ->
  [ Gamma ; Delta2 |- n :- A ] ->
  merge Delta1 Delta2 Delta ->
  [ Gamma ; Delta |- App m n :- App (TyLam B) n ]
| l_app2 Gamma Delta1 Delta2 Delta A B m n :
  [ Gamma ; Delta1 |- m :- Lolli A B ] ->
  [ Gamma ; Delta2 |- n :- A ] ->
  merge Delta1 Delta2 Delta ->
  [ Gamma ; Delta |- App m n :- B ]
| u_conv Gamma Delta A B m :
  [ Gamma ; pure Delta |- A :- U ] ->
  [ Gamma ; pure Delta |- B :- U ] ->
  A === B ->
  [ Gamma ; Delta |- m :- A ] ->
  [ Gamma ; Delta |- m :- B ]
| l_conv Gamma Delta A B m :
  [ Gamma ; pure Delta |- A :- L ] ->
  [ Gamma ; pure Delta |- B :- L ] ->
  A === B ->
  [ Gamma ; Delta |- m :- A ] ->
  [ Gamma ; Delta |- m :- B ]
where "[ Gamma ; Delta |- s :- A ]" := (has_type Gamma Delta s A).

Inductive context_ok : seq_opt term -> seq_opt term -> Prop :=
| nil_ok :
  [ nil ; nil |- ]
| u_ok Gamma Delta A :
  [ Gamma ; Delta |- ] ->
  [ Gamma ; pure Delta |- A :- U ] ->
  [ A ::: Gamma ; None :: Delta |- ]
| l_ok Gamma Delta A :
  [ Gamma ; pure Delta |- A :- L ] ->
  [ Gamma ; Delta |- ] ->
  [ None :: Gamma ; A ::: Delta |- ]
| n_ok Gamma Delta :
  [ Gamma ; Delta |- ] ->
  [ None :: Gamma ; None :: Delta |- ]
where "[ Gamma ; Delta |- ]" := (context_ok Gamma Delta).

Lemma pure_ok Gamma Delta :
  [ Gamma ; Delta |- ] ->
  [ Gamma ; pure Delta |- ].
Proof with eauto using context_ok.
  intros.
  induction H...
  - simpl.
    apply u_ok...
    rewrite pure_pure...
  - simpl.
    apply n_ok...
Qed.

Lemma merge_pure_inv T (Delta Delta1 Delta2 : seq_opt T) :
  merge Delta1 Delta2 Delta ->
  pure Delta1 = pure Delta /\ pure Delta2 = pure Delta.
Proof.
  intros.
  induction H; eauto.
  - destruct IHmerge.
    constructor.
    simpl; rewrite H0; eauto.
    simpl; rewrite H1; eauto.
  - destruct IHmerge.
    constructor.
    simpl; rewrite H0; eauto.
    simpl; rewrite H1; eauto.
Qed.

Lemma merge_inv_ok Gamma Delta :
  [ Gamma; Delta |- ] ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Delta ->
    [ Gamma; Delta1 |- ] /\ [ Gamma; Delta2 |- ].
Proof.
  intros.
  dependent induction H.
  - inversion H0.
    constructor.
    constructor; eauto.
    constructor; eauto.
  - inversion H1; subst.
    apply IHcontext_ok in H5.
    destruct H5.
    constructor; eauto.
    constructor; eauto.
    inversion H1; subst.
    apply merge_pure_inv in H5.
    destruct H5.
    rewrite H4; eauto.
    apply merge_pure_inv in H6.
    destruct H6.
    rewrite H4; eauto.
    constructor; eauto.
    inversion H1; subst.
    apply merge_pure_inv in H5.
    destruct H5.
    rewrite H5; eauto.
    apply merge_pure_inv in H6.
    destruct H6.
    rewrite H5; eauto.
    inversion H1; subst.
    apply merge_pure_inv in H5.
    apply IHcontext_ok in H3.
    destruct H5.
    destruct H3.
    constructor; eauto.
    constructor; eauto.
    rewrite H2; eauto.
    constructor; eauto.
    rewrite H4; eauto.
    apply merge_pure_inv in H5.
    apply IHcontext_ok in H4.
    destruct H5.
    destruct H4.
    constructor; eauto.
    constructor; eauto.
    rewrite H2; eauto.
    constructor; eauto.
    rewrite H3; eauto.
  - inversion H1; subst.
    inversion H1; subst.
    apply IHcontext_ok in H5.
    apply merge_pure_inv in H3.
    destruct H5.
    destruct H3.
    constructor; eauto.
    constructor; eauto.
    rewrite H3; eauto.
    constructor; eauto.
    inversion H1; subst.
    apply IHcontext_ok in H5.
    apply merge_pure_inv in H4.
    destruct H5.
    destruct H4.
    constructor; eauto.
    constructor; eauto.
    constructor; eauto.
    rewrite H5; eauto.
  - inversion H0; subst.
    inversion H0; subst.
    apply IHcontext_ok in H4.
    apply merge_pure_inv in H2.
    destruct H4.
    destruct H2.
    constructor; eauto.
    constructor; eauto.
    constructor; eauto.
    apply IHcontext_ok in H4.
    apply merge_pure_inv in H3.
    destruct H4.
    destruct H3.
    constructor; eauto.
    constructor; eauto.
    constructor; eauto.
    apply IHcontext_ok in H4.
    destruct H4.
    constructor; eauto.
    constructor; eauto.
    constructor; eauto.
Qed.

Lemma context_size Gamma Delta : 
  [ Gamma ; Delta |- ] -> size Gamma = size Delta.
Proof.
  intros.
  induction H; simpl; eauto.
Qed.

Lemma tyProd_inv Gamma Delta A B :
  [ Gamma ; Delta |- TyProd A B :- U ] ->
  [ Gamma ; Delta |- ] ->
  [ Gamma ; Delta |- A :- U ].
Proof.
  move e:(TyProd A B) => s tp. elim: tp A B e => //{Gamma Delta s}.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
  - move=> Gamma Delta A B m tp1 ih1 tp2 ih2 eqv tp3 ih3 A0 B0 eq wf.
    subst. 
    eapply u_conv.
    apply tp1.
    apply tp2.
    apply eqv.
    eapply ih3; eauto.
  - move=> Gamma Delta A B m tp1 ih1 tp2 ih2 eqv tp3 ih3 A0 B0 eq wf.
    subst.
    eapply l_conv.
    apply tp1.
    apply tp2.
    apply eqv.
    eapply ih3; eauto.
Qed.

Lemma arrow_inv Gamma Delta A B :
  [ Gamma ; Delta |- Arrow A B :- U ] ->
  [ Gamma ; Delta |- ] ->
  [ Gamma ; Delta |- A :- L ].
Proof.
  move e:(Arrow A B) => s tp. elim: tp A B e => //{Gamma Delta s}.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
Qed.

Lemma lnProd_inv Gamma Delta A B :
  [ Gamma ; Delta |- LnProd A B :- L ] ->
  [ Gamma ; Delta |- ] ->
  [ Gamma ; Delta |- A :- U ].
Proof.
  move e:(LnProd A B) => s tp. elim: tp A B e => //{Gamma Delta s}.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
Qed.

Lemma lolli_inv Gamma Delta A B :
  [ Gamma ; Delta |- Lolli A B :- L ] ->
  [ Gamma ; Delta |- ] ->
  [ Gamma ; Delta |- A :- L ].
Proof.
  move e:(Lolli A B) => s tp. elim: tp A B e => //{Gamma Delta s}.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
  - move=> Gamma Delta A B tp1 _ tp2 _ A0 B0 [->_] => //.
  - move=> Gamma Delta A B m tp1 ih1 tp2 ih2 eqv tp3 ih3 A0 B0 eq wf.
    subst. 
    eapply u_conv.
    apply tp1.
    apply tp2.
    apply eqv.
    eapply ih3; eauto.
  - move=> Gamma Delta A B m tp1 ih1 tp2 ih2 eqv tp3 ih3 A0 B0 eq wf.
    subst.
    eapply l_conv.
    apply tp1.
    apply tp2.
    apply eqv.
    eapply ih3; eauto.
Qed.

Inductive shift : 
  seq_opt term -> seq_opt term ->
  seq_opt term -> seq_opt term -> 
  nat -> (var -> var) -> Prop :=
| shift_O Gamma Delta : 
  shift Gamma Gamma Delta Delta 0 id
| shift_S Gamma Gamma1 Gamma2 Delta Delta1 Delta2 n xi :
  shift Gamma Gamma1 Delta Delta1 n xi ->
  (forall x A, has Gamma x A -> has Gamma2 (upren xi x) A.[ren (upren xi)]) ->
  (forall x A, has Delta x A -> has Delta2 (upren xi x) A.[ren (upren xi)]) ->
  (forall x A, only Delta x A -> only Delta2 (upren xi x) A.[ren (upren xi)]) ->
  (all_none Delta -> all_none Delta2) ->
  shift Gamma Gamma2 Delta Delta2 (n.+1) (upren xi).

Lemma shift_gamma_ok Gamma Gamma' Delta Delta' n xi :
  shift Gamma Gamma' Delta Delta' n xi ->
  forall A,
    shift (A ::: Gamma) (A.[ren xi] ::: Gamma') (None :: Delta)
      (None :: Delta') n (upren xi).
Proof.
  intro H.
  dependent induction H.
  - intros.
    asimpl.
    constructor.
  - intros.
    econstructor.
    apply IHshift.
    intros.
    inversion H4; subst.
    asimpl.
    replace (A.[ren (1 .: xi >>> (+2))]) with 
      (A.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor.
    asimpl.
    replace (A1.[ren (1 .: xi >>> (+2))]) with 
      (A1.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    intros.
    inversion H4; subst.
    asimpl.
    replace (A1.[ren (1 .: xi >>> (+2))]) with 
      (A1.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    intros.
    inversion H4; subst.
    asimpl.
    replace (A1.[ren (1 .: xi >>> (+2))]) with 
      (A1.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    intros.
    inversion H4; subst.
    constructor; eauto.
Qed.

Lemma shift_delta_ok Gamma Gamma' Delta Delta' n xi :
  shift Gamma Gamma' Delta Delta' n xi ->
  forall A,
    shift (None :: Gamma) (None :: Gamma') (A ::: Delta)
      (A.[ren xi] ::: Delta') n (upren xi).
Proof.
  intros H.
  induction H.
  - intros.
    asimpl.
    constructor.
  - intros.
    econstructor.
    apply IHshift.
    intros.
    inversion H4; subst.
    asimpl.
    replace (A1.[ren (1 .: xi >>> (+2))]) with 
      (A1.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    intros.
    inversion H4; subst.
    asimpl.
    replace (A.[ren (1 .: xi >>> (+2))]) with 
      (A.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    asimpl.
    replace (A1.[ren (1 .: xi >>> (+2))]) with 
      (A1.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    intros.
    inversion H4; subst.
    asimpl.
    replace (A.[ren (1 .: xi >>> (+2))]) with 
      (A.[ren (upren xi)].[ren (+1)]) by autosubst.
    constructor; eauto.
    intros.
    inversion H4; subst.
Qed.

Lemma shift_only Delta :
  forall Gamma Gamma' Delta' n xi x A,
    shift Gamma Gamma' Delta Delta' n xi ->
    only Delta x A ->
    only Delta' (xi x) A.[ren xi].
Proof.
  induction Delta.
  - intros.
    inversion H0.
  - intros.
    inversion H; subst.
    inversion H0; subst.
    asimpl.
    constructor; eauto.
    asimpl.
    constructor; eauto.
    eauto.
Qed.

Lemma shift_pure Gamma Gamma' Delta Delta' n xi :
  shift Gamma Gamma' (pure Delta) Delta' n xi ->
  Delta' = pure Delta'.
Proof.
  intros.
  dependent induction H.
  - rewrite pure_pure; eauto.
  - assert (all_none (pure Delta)).
    eapply pure_all_none; eauto.
    apply H3 in H4.
    apply all_none_pure in H4.
    rewrite H4; eauto.
Qed.

Lemma shift_pure_pure Gamma Gamma' Delta Delta' n xi :
  shift Gamma Gamma' Delta Delta' n xi ->
  shift Gamma Gamma' (pure Delta) (pure Delta') n xi.
Proof.
  intro H.
  induction H.
  - constructor.
  - econstructor.
    apply IHshift.
    eauto.
    intros.
    apply has_pure in H4; inversion H4.
    intros.
    apply only_pure in H4; inversion H4.
    intros.
    eapply pure_all_none; eauto.
Qed.

Lemma shift_inv_0 Gamma Gamma' Delta Delta' :
  shift Gamma Gamma' Delta Delta' 0 id ->
  Gamma = Gamma' /\ Delta = Delta'.
Proof.
  intro H.
  dependent induction H.
  constructor; eauto.
Qed.

Lemma merge_shift0 Delta :
  forall Delta1 Delta2 Gamma, 
    merge Delta1 Delta2 Delta ->
    shift Gamma Gamma Delta1 Delta 0 id.
Proof.
  induction Delta.
  - intros.
    inversion H.
    constructor.
  - intros.
    inversion H; subst.
    pose proof (IHDelta _ _ Gamma H3).
    apply shift_inv_0 in H0.
    firstorder.
    rewrite H1.
    constructor.
    pose proof (IHDelta _ _ Gamma H3).
    apply shift_inv_0 in H0.
    firstorder.
    rewrite H1.



Lemma merge_shift1 Gamma Gamma' Delta Delta' xi :
  shift Gamma Gamma' Delta Delta' xi ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Delta ->
    shift Gamma Gamma' Delta1 Delta' xi.
Proof.
  intro.
  induction H.
  - intros.
    constructor.

Lemma merge_shift Gamma Gamma' Delta Delta' xi :
  shift Gamma Gamma' Delta Delta' xi ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Delta ->
    exists Delta1' Delta2',
      merge Delta' Delta2' Delta' /\
      shift Gamma Gamma' Delta1 Delta1' xi /\
      shift Gamma Gamma' Delta2 Delta2' xi.
Proof.
  intro.
  induction H.
  - intros.
      


Lemma rename_shift Gamma Delta m A :
  [ Gamma ; Delta |- ] ->
  [ Gamma ; Delta |- m :- A ] ->
  forall Gamma' Delta' xi,
    shift Gamma Gamma' Delta Delta' xi ->
    [ Gamma'; Delta' |- m.[ren xi] :- A.[ren xi] ].
Proof.
  intros.
  dependent induction H0.
  - asimpl.
    apply shift_pure in H1.
    rewrite H1.
    constructor.
  - asimpl.
    apply shift_pure in H1.
    rewrite H1.
    constructor.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply u_prod1.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    replace U with (U.[ren (upren xi)]) by autosubst.
    replace (None :: pure Delta') with (pure (None :: Delta')) by autosubst.
    eapply IHhas_type2.
    econstructor.
    apply H.
    rewrite pure_pure; eauto.
    simpl.
    apply shift_gamma_ok; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply u_prod2.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    replace U with (U.[ren (upren xi)]) by autosubst.
    replace (None :: pure Delta') with (pure (None :: Delta')) by autosubst.
    eapply IHhas_type2.
    econstructor.
    apply H.
    rewrite pure_pure; eauto.
    simpl.
    apply shift_gamma_ok; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply l_prod1.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    replace U with (U.[ren (upren xi)]) by autosubst.
    replace (None :: pure Delta') with (pure (None :: Delta')) by autosubst.
    eapply IHhas_type2.
    econstructor.
    apply H.
    rewrite pure_pure; eauto.
    simpl.
    apply shift_gamma_ok; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply l_prod2.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    replace U with (U.[ren (upren xi)]) by autosubst.
    replace (None :: pure Delta') with (pure (None :: Delta')) by autosubst.
    eapply IHhas_type2.
    econstructor.
    apply H.
    rewrite pure_pure; eauto.
    simpl.
    apply shift_gamma_ok; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply arrow1.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    eapply IHhas_type2; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply arrow2.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    eapply IHhas_type2; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply lolli1.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    eapply IHhas_type2; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply lolli2.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    eapply IHhas_type2; eauto.
    rewrite <- H0; eauto.
  - replace ((Var x).[ren xi]) with (Var (xi x)) by autosubst.
    pose proof (shift_pure H1).
    rewrite H2.
    apply u_var.
    inversion H1; subst.
    asimpl; eauto.
    eauto.
  - replace ((Var x).[ren xi]) with (Var (xi x)) by autosubst.
    apply l_var.
    eapply shift_only; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply u_lam1.
    replace (TyProd A.[ren xi] B.[ren (upren xi)]) 
      with ((TyProd A B).[ren xi]) by autosubst.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    replace (None :: pure Delta') with (pure (None :: Delta')) by autosubst.
    eapply IHhas_type2; eauto.
    constructor; eauto.
    rewrite pure_pure; eauto.
    eapply tyProd_inv; eauto.
    simpl.
    rewrite <- H0; eauto.
    apply shift_gamma_ok; eauto.
  - asimpl.
    pose proof (shift_pure H1).
    rewrite H0.
    apply u_lam2.
    replace (Arrow A.[ren xi] B.[ren xi]) 
      with ((Arrow A B).[ren xi]) by autosubst.
    eapply IHhas_type1; eauto.
    rewrite <- H0; eauto.
    replace (B.[ren xi].[ren (+1)]) 
      with (B.[ren (+1)].[ren (upren xi)]) by autosubst.
    eapply IHhas_type2; eauto.
    constructor; eauto.
    rewrite pure_pure; eauto.
    eapply arrow_inv; eauto.
    apply shift_delta_ok; eauto.
    rewrite <- H0; eauto.
  - asimpl.
    apply l_lam1.
    replace (LnProd A.[ren xi] B.[ren (upren xi)]) 
      with ((LnProd A B).[ren xi]) by autosubst.
    eapply IHhas_type1; eauto.
    apply pure_ok; eauto.
    apply shift_pure_pure; eauto.
    eapply IHhas_type2; eauto.
    constructor; eauto.
    eapply lnProd_inv; eauto.
    apply pure_ok; eauto.
    apply shift_gamma_ok; eauto.
  - asimpl.
    apply l_lam2.
    replace (Lolli A.[ren xi] B.[ren xi]) 
      with ((Lolli A B).[ren xi]) by autosubst.
    eapply IHhas_type1; eauto.
    apply pure_ok; eauto.
    apply shift_pure_pure; eauto.
    replace (B.[ren xi].[ren (+1)]) 
      with (B.[ren (+1)].[ren (upren xi)]) by autosubst.
    eapply IHhas_type2; eauto.
    constructor; eauto.
    eapply lolli_inv; eauto.
    apply pure_ok; eauto.
    apply shift_delta_ok; eauto.
  - asimpl.
    eapply u_app1.
    pose proof (merge_inv_ok H H0).
    pose proof (merge_shift H1 H0).
    firstorder.
    specialize (H7 Gamma' x0 xi H6).
    specialize (H8 Gamma' x xi H5). asimpl in H8.
    apply H8.
    apply H7.
    apply H3.

    






Lemma has_ok Gamma Delta :
  [ Gamma ; Delta |- ] ->
    forall x A,
      has Gamma x A ->
      [ Gamma ; pure Delta |- A :- U ].
Proof with eauto using has_type.
  intros.
  induction H.
  - inversion H0.
  - inversion H0; subst.

Lemma value_typing Gamma Delta v A :
  [ Gamma ; Delta |- ] ->
  [ Gamma ; Delta |- v :- A ] -> value v ->
  [ Gamma ; Delta |- A :- U ] \/ [ Gamma ; Delta |- A :- L ].
Proof with eauto using has_type.
  intros.
  induction H0...
  - destruct H. inversion H0.
  -