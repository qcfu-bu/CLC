From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Validity of CLC types 

  Types of well-typed terms are themselves well-sorted. *)

Lemma merge_context_ok_inv Γ Γ1 Γ2 :
  merge Γ1 Γ2 Γ ->
  [ Γ |- ] ->
  [ Γ1 |- ] /\ [ Γ2 |- ].
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

Theorem validity Γ m A : 
  [ Γ |- ] ->
  [ Γ |- m :- A ] ->
  exists s l, [ re Γ |- A :- Sort s l ].
Proof.
  intros.
  dependent induction H0.
  - exists U; exists l.+2.
    constructor.
    rewrite <- pure_re; eauto.
  - exists U; exists l.+1.
    constructor.
    rewrite <- pure_re; eauto.
  - exists U; exists l.+1.
    constructor.
    rewrite <- pure_re; eauto.
  - exists U; exists l.+1.
    constructor.
    rewrite <- pure_re; eauto.
  - exists U; exists l.+1.
    constructor.
    rewrite <- pure_re; eauto.
  - exists U.
    eapply hasU_ok; eauto.
  - exists L.
    eapply hasL_ok; eauto.
  - exists t; exists l.
    rewrite <- pure_re; eauto.
  - exists t; exists l; eauto.
  - pose proof (merge_pure2 H1 H0).
    pose proof (merge_re_re H1). inv H3.
    apply merge_context_ok_inv in H1; eauto. first_order.
    apply u_arrow_inv in H2. first_order.
    exists x3; exists x4.
    replace (Sort x3 x4) with ((Sort x3 x4).[n/]) by autosubst.
    eapply substitutionU; eauto.
    replace (Γ2) with (re Γ1).
    apply merge_re_re_re.
    apply pure_re in H0.
    rewrite H0.
    rewrite H5; eauto.
  - pose proof (merge_re_re H0). inv H1.
    apply merge_context_ok_inv in H0; eauto. first_order.
    eapply l_arrow_inv in H5. first_order.
    exists x3; exists x4.
    replace (Sort x3 x4) with ((Sort x3 x4).[n/]) by autosubst.
    eapply substitutionN; eauto.
    rewrite <- H2; eauto.
  - pose proof (merge_pure2 H1 H0).
    pose proof (merge_re_re H1). inv H3.
    apply merge_context_ok_inv in H1; eauto. first_order.
    apply u_lolli_inv in H2. first_order.
    exists x3; exists x4.
    replace (Sort x3 x4) with ((Sort x3 x4).[n/]) by autosubst.
    eapply substitutionU; eauto.
    replace (Γ2) with (re Γ1).
    apply merge_re_re_re.
    apply pure_re in H0.
    rewrite H0.
    rewrite H5; eauto.
  - pose proof (merge_re_re H0). inv H1.
    apply merge_context_ok_inv in H0; eauto. first_order.
    eapply l_lolli_inv in H5. first_order.
    exists x3; exists x4.
    replace (Sort x3 x4) with ((Sort x3 x4).[n/]) by autosubst.
    eapply substitutionN; eauto.
    rewrite <- H2; eauto.
  - exists s; exists l; eauto.
Qed.