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
  
Inductive has_type : seq term -> seq_opt term -> term -> term -> Prop :=
| u_axiom Gamma : 
  [ Gamma ; nil |- U :- U ]
| l_axiom Gamma :
  [ Gamma ; nil |- L :- U ]
| u_prod1 Gamma A B :
  [ Gamma ; nil |- A :- U ] ->
  [ A :: Gamma ; nil |- B :- U ] ->
  [ Gamma ; nil |- TyProd A B :- U ]
| u_prod2 Gamma A B :
  [ Gamma ; nil |- A :- U ] ->
  [ A :: Gamma ; nil |- B :- L ] ->
  [ Gamma ; nil |- TyProd A B :- U ]
| l_prod1 Gamma A B :
  [ Gamma ; nil |- A :- U ] ->
  [ A :: Gamma ; nil |- B :- U ] ->
  [ Gamma ; nil |- LnProd A B :- L ]
| l_prod2 Gamma A B :
  [ Gamma ; nil |- A :- U ] ->
  [ A :: Gamma ; nil |- B :- L ] ->
  [ Gamma ; nil |- LnProd A B :- L ]
| arrow1 Gamma A B :
  [ Gamma ; nil |- A :- L ] ->
  [ Gamma ; nil |- B :- U ] ->
  [ Gamma ; nil |- Arrow A B :- U ]
| arrow2 Gamma A B :
  [ Gamma ; nil |- A :- L ] ->
  [ Gamma ; nil |- B :- L ] ->
  [ Gamma ; nil |- Arrow A B :- U ]
| lolli1 Gamma A B :
  [ Gamma ; nil |- A :- L ] ->
  [ Gamma ; nil |- B :- U ] ->
  [ Gamma ; nil |- Lolli A B :- L ]
| lolli2 Gamma A B :
  [ Gamma ; nil |- A :- L ] ->
  [ Gamma ; nil |- B :- L ] ->
  [ Gamma ; nil |- Lolli A B :- L ]
| u_var Gamma x : 
  x < size Gamma ->
  [ Gamma ; nil |- Var x :- Gamma`_x ]
| l_var Gamma Delta x A :
  only Delta x A ->
  [ Gamma ; Delta |- Var x :- A ]
| u_lam1 Gamma n A B :
  [ Gamma ; nil |- TyProd A B :- U ] ->
  [ A :: Gamma ; nil |- n :- B ] ->
  [ Gamma ; nil |- TyLam n :- TyProd A B ]
| u_lam2 Gamma n A B :
  [ Gamma ; nil |- Arrow A B :- U ] ->
  [ A :: Gamma ; nil |- n :- B ] ->
  [ Gamma ; nil |- TyLam n :- Arrow A B ]
| l_lam1 Gamma Delta n A B :
  [ Gamma ; nil |- LnProd A B :- L ] ->
  [ A :: Gamma ; Delta |- n :- B ] ->
  [ Gamma ; Delta |- LnLam n :- LnProd A B ]
| l_lam2 Gamma Delta n A B :
  [ Gamma ; nil |- Lolli A B :- L ] ->
  [ Gamma ; A ::: Delta |- n :- B ] ->
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
where "[ Gamma ; Delta |- s :- A ]" := (has_type Gamma Delta s A).

Inductive context_ok : seq term -> seq_opt term -> Prop :=
| nil_ok :
  [ nil ; nil |- ]
| u_ok Gamma A :
  [ Gamma ; nil |- ] ->
  [ Gamma ; nil |- A :- U ] ->
  [ A :: Gamma ; nil |- ]
| l_ok Gamma Delta A :
  [ Gamma ; Delta |- ] ->
  [ Gamma ; nil |- A :- L ] ->
  [ Gamma ; A ::: Delta |- ]
where "[ Gamma ; Delta |- ]" := (context_ok Gamma Delta).