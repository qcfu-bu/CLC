From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Subject Reduction of CLC 

  Well-typed CLC terms always reduce to well-types terms of the same type. *)

Theorem subject_reduction Γ m A :
  [ Γ |- ] ->
  [ Γ |- m :- A ] ->
  forall n, m ~> n -> [ Γ |- n :- A ].
Proof.
  intros.
  dependent induction H0.
  - inv H1.
  - inv H1.
  - inv H1.
    + specialize (IHhas_type1 H _ H6).
      eapply prop; eauto.
      eapply context_convU.
      eapply conv1i; eauto.
      rewrite <- pure_re; eauto.
      eauto.
    + assert ([A +u Γ |-]).
      eapply u_ok; eauto.
      rewrite <-pure_re; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply prop; eauto.
  - inv H1.
    + specialize (IHhas_type1 H _ H6).
      eapply u_prod; eauto.
      eapply context_convU.
      eapply conv1i; eauto.
      repeat rewrite <- pure_re; eauto.
      eauto.
    + assert ([A +u Γ |-]).
      eapply u_ok; eauto; repeat rewrite <-pure_re; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply u_prod; eauto.
  - inv H1.
    + specialize (IHhas_type1 H _ H6).
      eapply l_prod; eauto.
    + assert ([□ Γ |-]).
      eapply n_ok; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply l_prod; eauto.
  - inv H1.
    + specialize (IHhas_type1 H _ H6).
      eapply u_lolli; eauto.
      eapply context_convU.
      eapply conv1i; eauto.
      repeat rewrite <- pure_re; eauto.
      eauto.
    + assert ([A +u Γ |-]).
      eapply u_ok; eauto; repeat rewrite <-pure_re; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply u_lolli; eauto.
  - inv H1.
    + specialize (IHhas_type1 H _ H6).
      eapply l_lolli; eauto.
    + assert ([□ Γ |-]).
      eapply n_ok; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply l_lolli; eauto.
  - inv H1.
  - inv H1.
  - inv H1.
    pose proof (pure_re H0).
    pose proof H0_.
    rewrite H1 in H0_.
    destruct s.
    + apply u_prod_inv in H0_. first_order.
      assert ([A +u Γ |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H6 _ H3).
      eapply prod_lam; eauto.
    + apply l_prod_inv in H0_. first_order.
      assert ([A +l Γ |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H6 _ H3).
      eapply prod_lam; eauto.
  - inv H1.
    pose proof H0_.
    destruct s.
    + apply u_lolli_inv in H0_; first_order.
      assert ([A +u Γ |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H4 _ H2).
      eapply lolli_lam; eauto.
    + apply l_lolli_inv in H0_; first_order.
      assert ([A +l Γ |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H4 _ H2).
      eapply lolli_lam; eauto.
  - pose proof (merge_context_ok_inv H1 H). inv H3.
    inv H2.
    + pose proof (validity H4 H0_); first_order.
      eapply substitutionU; eauto.
      eapply prod_lam_inv in H0_; eauto.
    + specialize (IHhas_type1 H4 _ H8).
      eapply u_prod_app; eauto.
    + specialize (IHhas_type2 H5 _ H8).
      assert (B.[n'/] === B.[n/]).
      apply conv_beta.
      apply conv1i; eauto.
      apply conv_sub in H2.
      pose proof (validity H4 H0_); first_order.
      apply u_prod_inv in H3; first_order.
      assert ([%Γ |- B.[n/] :- (Sort x1 x2).[n/] ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0).
      pose proof (merge_re_re H1). inv H9.
      rewrite H7. rewrite H10. rewrite H11.
      apply merge_re_re_re.
      eapply conversion; eauto.
      eapply u_prod_app; eauto.
  - pose proof (merge_context_ok_inv H0 H). inv H2.
    inv H1.
    + pose proof (validity H3 H0_); first_order.
      eapply substitutionL; eauto.
      eapply prod_lam_inv in H0_; eauto.
    + specialize (IHhas_type1 H3 _ H7).
      eapply l_prod_app; eauto.
    + specialize (IHhas_type2 H4 _ H7).
      assert (B.[n'/] === B.[n/]).
      apply conv_beta.
      apply conv1i; eauto.
      apply conv_sub in H1.
      pose proof (validity H3 H0_); first_order.
      apply l_prod_inv in H2; first_order.
      assert ([%Γ |- B.[n/] :- (Sort x1 x2).[n/] ]).
      eapply substitutionN; eauto.
      pose proof (merge_re_re H0). inv H6.
      rewrite <-H8; eauto.
      eapply conversion; eauto.
      eapply l_prod_app; eauto.
  - pose proof (merge_context_ok_inv H1 H). inv H3.
    inv H2.
    + pose proof (validity H4 H0_); first_order.
      eapply substitutionU; eauto.
      eapply lolli_lam_inv in H0_; eauto.
    + specialize (IHhas_type1 H4 _ H8).
      eapply u_lolli_app; eauto.
    + specialize (IHhas_type2 H5 _ H8).
      assert (B.[n'/] === B.[n/]).
      apply conv_beta.
      apply conv1i; eauto.
      apply conv_sub in H2.
      pose proof (validity H4 H0_); first_order.
      apply u_lolli_inv in H3; first_order.
      assert ([%Γ |- B.[n/] :- (Sort x1 x2).[n/] ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0).
      pose proof (merge_re_re H1). inv H9.
      rewrite H7. rewrite H10. rewrite H11.
      apply merge_re_re_re.
      eapply conversion; eauto.
      eapply u_lolli_app; eauto.
  - pose proof (merge_context_ok_inv H0 H). inv H2.
    inv H1.
    + pose proof (validity H3 H0_); first_order.
      eapply substitutionL; eauto.
      eapply lolli_lam_inv in H0_; eauto.
    + specialize (IHhas_type1 H3 _ H7).
      eapply l_lolli_app; eauto.
    + specialize (IHhas_type2 H4 _ H7).
      assert (B.[n'/] === B.[n/]).
      apply conv_beta.
      apply conv1i; eauto.
      apply conv_sub in H1.
      pose proof (validity H3 H0_); first_order.
      apply l_lolli_inv in H2; first_order.
      assert ([%Γ |- B.[n/] :- (Sort x1 x2).[n/] ]).
      eapply substitutionN; eauto.
      pose proof (merge_re_re H0). inv H6.
      rewrite <-H8; eauto.
      eapply conversion; eauto.
      eapply l_lolli_app; eauto.
  - eapply conversion; eauto.
Qed.

Theorem subject_reduction_red m n :
  m ~>* n ->
  forall Γ A,
    [ Γ |- ] ->
    [ Γ |- m :- A ] ->
    [ Γ |- n :- A ].
Proof.
  intro H.
  dependent induction H; intros; eauto.
  eapply subject_reduction.
  apply H1.
  apply IHstar; eauto.
  apply H0.
Qed.

Lemma canonical_prod m C :
  [ nil |- m :- C ] -> value m ->
  forall A B s, 
    C <: Prod A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - inv H.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma canonical_lolli m C :
  [ nil |- m :- C ] -> value m ->
  forall A B s, 
    C <: Lolli A B s -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - inv H.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

(** * Progress of CLC 

  Well-typed CLC terms under an empty context never get stuck.
  They are either values or could reduce. *)

Theorem progress m A :
  [ nil |- m :- A ] -> value m \/ exists n, step m n.
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
      eapply canonical_prod; eauto.
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
      eapply canonical_prod; eauto.
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
      eapply canonical_lolli; eauto.
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