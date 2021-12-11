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
      eapply u_arrow; eauto.
      eapply context_convU.
      eapply conv1i; eauto.
      repeat rewrite <- pure_re; eauto.
      eauto.
    + assert ([A +u Γ |-]).
      eapply u_ok; eauto; repeat rewrite <-pure_re; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply u_arrow; eauto.
  - inv H1.
    + specialize (IHhas_type1 H _ H6).
      eapply l_arrow; eauto.
    + assert ([□ Γ |-]).
      eapply n_ok; eauto.
      specialize (IHhas_type2 H1 _ H6).
      eapply l_arrow; eauto.
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
  - pose proof (pure_re H0).
    rewrite H2 in H0_.
    pose proof H0_.
    inv H1.
    destruct s.
    + assert (Arrow A B U ~> Arrow A' B U).
      constructor; eauto.
      specialize (IHhas_type1 H _ H1).
      apply u_arrow_inv in H3; first_order.
      apply: conversion.
      apply: conv_sub.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      apply: arrow_lam; eauto.
      apply: context_convU.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      eauto.
    + assert (Arrow A B L ~> Arrow A' B L).
      constructor; eauto.
      specialize (IHhas_type1 H _ H1).
      apply l_arrow_inv in H3; first_order.
      apply: conversion.
      apply: conv_sub.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      apply: arrow_lam; eauto.
      apply: context_convL.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      eauto.
    destruct s.
    + apply u_arrow_inv in H0_. first_order.
      assert ([A +u Γ |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H5 _ H8).
      eapply arrow_lam; eauto.
      rewrite <-pure_re in H3; eauto.
    + apply l_arrow_inv in H0_. first_order.
      assert ([A +l Γ |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H5 _ H8).
      eapply arrow_lam; eauto.
      rewrite <-pure_re in H3; eauto.
  - pose proof H0_.
    pose proof (re_ok H).
    inv H1.
    destruct s.
    + assert (Lolli A B U ~> Lolli A' B U).
      constructor; eauto.
      specialize (IHhas_type1 H2 _ H1).
      apply u_lolli_inv in H0; first_order.
      apply: conversion.
      apply: conv_sub.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      apply: lolli_lam; eauto.
      apply: context_convU.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      eauto.
    + assert (Lolli A B L ~> Lolli A' B L).
      constructor; eauto.
      specialize (IHhas_type1 H2 _ H1).
      apply l_lolli_inv in H0; first_order.
      apply: conversion.
      apply: conv_sub.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      apply: lolli_lam; eauto.
      apply: context_convL.
      apply: conv_sym.
      apply: conv1; eauto.
      eauto.
      eauto.
    destruct s.
    + apply u_lolli_inv in H0_. first_order.
      assert ([A +u Γ |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H4 _ H7).
      eapply lolli_lam; eauto.
    + apply l_lolli_inv in H0_. first_order.
      assert ([A +l Γ |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H4 _ H7).
      eapply lolli_lam; eauto.
  - pose proof (merge_context_ok_inv H1 H). inv H3.
    inv H2.
    + pose proof (validity H4 H0_); first_order.
      eapply substitutionU; eauto.
      eapply arrow_lam_inv in H0_; eauto.
    + specialize (IHhas_type1 H4 _ H8).
      eapply u_arrow_app; eauto.
    + specialize (IHhas_type2 H5 _ H8).
      assert (B.[n'/] === B.[n/]).
      apply conv_beta.
      apply conv1i; eauto.
      apply conv_sub in H2.
      pose proof (validity H4 H0_); first_order.
      apply u_arrow_inv in H3; first_order.
      assert ([%Γ |- B.[n/] :- (Sort x1 x2).[n/] ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0).
      pose proof (merge_re_re H1). inv H9.
      rewrite H7. rewrite H10. rewrite H11.
      apply merge_re_re_re.
      eapply conversion; eauto.
      eapply u_arrow_app; eauto.
  - pose proof (merge_context_ok_inv H0 H). inv H2.
    inv H1.
    + pose proof (validity H3 H0_); first_order.
      eapply substitutionL; eauto.
      eapply arrow_lam_inv in H0_; eauto.
    + specialize (IHhas_type1 H3 _ H7).
      eapply l_arrow_app; eauto.
    + specialize (IHhas_type2 H4 _ H7).
      assert (B.[n'/] === B.[n/]).
      apply conv_beta.
      apply conv1i; eauto.
      apply conv_sub in H1.
      pose proof (validity H3 H0_); first_order.
      apply l_arrow_inv in H2; first_order.
      assert ([%Γ |- B.[n/] :- (Sort x1 x2).[n/] ]).
      eapply substitutionN; eauto.
      pose proof (merge_re_re H0). inv H6.
      rewrite <-H8; eauto.
      eapply conversion; eauto.
      eapply l_arrow_app; eauto.
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

Lemma canonical_arrow m C :
  [ nil |- m :- C ] -> value m ->
  forall A B s, 
    C <: Arrow A B s -> exists A' m' s', m = Lam A' m' s'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - inv H.
  - exists A. exists n. exists s. eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma canonical_lolli m C :
  [ nil |- m :- C ] -> value m ->
  forall A B s, 
    C <: Lolli A B s -> exists A' m' s', m = Lam A' m' s'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - inv H.
  - exists A. exists n. exists s. eauto.
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
    + assert (exists A' m' s', m = Lam A' m' s').
      eapply canonical_arrow; eauto.
      first_order; subst.
      exists (x0.[n/]).
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
    + assert (exists A' m' s', m = Lam A' m' s').
      eapply canonical_arrow; eauto.
      first_order; subst.
      exists (x0.[n/]).
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
    + assert (exists A' m' s', m = Lam A' m' s').
      eapply canonical_lolli; eauto.
      first_order; subst.
      exists (x0.[n/]).
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
    + assert (exists A' m' s', m = Lam A' m' s').
      eapply canonical_lolli; eauto.
      first_order; subst.
      exists (x0.[n/]).
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