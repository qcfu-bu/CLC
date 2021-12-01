From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Inversion Lemmas for CLC typing. *)

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

Lemma u_prod_inv Γ A B s :
  [ Γ |- Prod A B U :- s ] -> 
  exists s l,
    [ Γ |- A :- Sort U l ] /\ [ A +u Γ |- B :- Sort s l ].
Proof.
  move e:(Prod A B U) => n tp. elim: tp A B e => //{Γ n s}.
  move=> Γ A B l0 p tp1 _ tp2 _ A0 B0 [->->].
    exists U.
    exists l0; firstorder.
    destruct l0; eauto.
    assert (𝐏 <: U @ n).
    apply sub_prop.
    eapply conversion; eauto.
    constructor; apply re_pure.
  move=> Γ A B s l0 p tp1 ih1 tp2 ih2 A0 B0 [->->].
    exists s.
    exists (Some l0); firstorder.
Qed.

Lemma l_prod_inv Γ A B s :
  [ Γ |- Prod A B L :- s ] -> 
  exists s l,
    [ Γ |- A :- Sort L l ] /\ [ □ Γ |- B :- Sort s l ].
Proof.
  move e:(Prod A B L) => n tp. elim: tp A B e => //{Γ n s}.
  move=> Γ A B s l0 p tp1 ih1 tp2 ih2 A0 B0 [->->].
    exists s.
    exists (Some l0); firstorder.
Qed.

Lemma u_lolli_inv Γ A B s :
  [ Γ |- Lolli A B U :- s ] -> 
  exists s l,
    [ Γ |- A :- Sort U l ] /\ [ A +u Γ |- B :- Sort s l ].
Proof.
  move e:(Lolli A B U) => n tp. elim: tp A B e => //{Γ n s}.
  move=> Γ A B s l0 p tp1 ih1 tp2 ih2 A0 B0 [->->].
    exists s.
    exists (Some l0); firstorder.
Qed.

Lemma l_lolli_inv Γ A B s :
  [ Γ |- Lolli A B L :- s ] -> 
  exists s l,
    [ Γ |- A :- Sort L l ] /\ [ □ Γ |- B :- Sort s l ].
Proof.
  move e:(Lolli A B L) => n tp. elim: tp A B e => //{Γ n s}.
  move=> Γ A B s l0 p tp1 ih1 tp2 ih2 A0 B0 [->->].
    exists s.
    exists (Some l0); firstorder.
Qed.

Lemma prod_lam_invX Γ n C :
  [ Γ |- Lam n :- C ] -> 
  forall A B s t l, 
    (C <: Prod A B s /\ [ %(A +{s} Γ) |- B :- Sort t l ]) ->
    [ A +{s} Γ |- n :- B ].
Proof.
  intros.
  dependent induction H; firstorder.
  - pose proof (sub_prod_inv H2).
    first_order; subst.
    pose proof (pure_re H).
    rewrite H6 in H0.
    destruct s0.
    + apply u_prod_inv in H0; first_order.
      eapply conversion; eauto.
      eapply context_convU.
      apply conv_sym; apply H4.
      apply H0.
      apply H1.
    + apply l_prod_inv in H0; first_order.
      eapply conversion; eauto.
      eapply context_convL.
      apply conv_sym; apply H4.
      apply H0.
      apply H1.
  - exfalso; solve_sub.
  - eapply IHhas_type2; eauto.
    split.
    eapply sub_trans; eauto.
    apply H3.
Qed.

Lemma lolli_lam_invX Γ n C :
  [ Γ |- Lam n :- C ] -> 
  forall A B s t l, 
    (C <: Lolli A B s /\ [ %(A +{s} Γ) |- B :- Sort t l ]) ->
    [ A +{s} Γ |- n :- B ].
Proof.
  intros.
  dependent induction H; firstorder.
  - exfalso; solve_sub.
  - pose proof (sub_lolli_inv H1).
    first_order; subst.
    destruct s0.
    + apply u_lolli_inv in H; first_order.
      eapply conversion; eauto.
      eapply context_convU.
      apply conv_sym; apply H3.
      apply H.
      apply H0.
    + apply l_lolli_inv in H; first_order.
      eapply conversion; eauto.
      eapply context_convL.
      apply conv_sym; apply H3.
      apply H.
      apply H0.
  - eapply IHhas_type2; eauto.
    split.
    eapply sub_trans; eauto.
    apply H3.
Qed.

Lemma prod_lam_inv Γ n A B s t l :
  [ %Γ |- Prod A B s :- Sort t l ] ->
  [ Γ |- Lam n :- Prod A B s ] -> 
  [ A +{s} Γ |- n :- B ].
Proof.
  intros.
  destruct s.
  - apply u_prod_inv in H; inv H; firstorder.
    eapply prod_lam_invX; eauto.
  - apply l_prod_inv in H; inv H; firstorder.
    eapply prod_lam_invX; eauto.
Qed.

Lemma lolli_lam_inv Γ n A B s t l :
  [ %Γ |- Lolli A B s:- Sort t l ] ->
  [ Γ |- Lam n :- Lolli A B s ] -> 
  [ A +{s} Γ |- n :- B ].
Proof.
  intros.
  destruct s.
  - apply u_lolli_inv in H; inv H; firstorder.
    eapply lolli_lam_invX; eauto.
  - apply l_lolli_inv in H; inv H; firstorder.
    eapply lolli_lam_invX; eauto.
Qed.