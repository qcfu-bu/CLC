From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Typed Substitution Lemma of CLC 

  The substitution lemma for CLC corresponds to cut elimination
  of linear logic. Due to rejection of weakening and contraction
  for linear variables, the contexts of substitution must be 
  precisely tracked at all times. This is accomplished by the
  agree_subst Δ σ Γ relation. Morally, this is similar to the
  agree_ren relation used for the proof of weakening. *)

Reserved Notation "[ Δ |- σ -| Γ ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil σ :
  [ nil |- σ -| nil ]
| agree_subst_u Δ σ Γ A :
  [ Δ |- σ -| Γ ] ->
  [ A.[σ] +u Δ |- up σ -| A +u Γ ]
| agree_subst_l Δ σ Γ A :
  [ Δ |- σ -| Γ ] ->
  [ A.[σ] +l Δ |- up σ -| A +l Γ ]
| agree_subst_n Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  [ +n Δ |- up σ -| +n Γ ]
| agree_subst_wkU Δ σ Γ n A :
  [ Δ |- σ -| Γ ] ->
  [ re Δ |- n :- A.[σ] ] ->
  [ Δ |- n .: σ -| A +u Γ ]
| agree_subst_wkL Δ1 Δ2 Δ σ Γ n A :
  merge Δ1 Δ2 Δ ->
  [ Δ1 |- σ -| Γ ] ->
  [ Δ2 |- n :- A.[σ] ] ->
  [ Δ |- n .: σ -| A +l Γ ]
| agree_subst_wkN Δ σ Γ n :
  [ Δ |- σ -| Γ ] ->
  [ Δ |- n .: σ -| +n Γ ]
| agree_subst_convU Δ σ Γ A B l :
  A <: B ->
  [ re Δ |- B.[ren (+1)].[σ] :- Sort U l ] ->
  [ Δ |- σ -| A +u Γ ] ->
  [ Δ |- σ -| B +u Γ ]
| agree_subst_convL Δ σ Γ A B l :
  A <: B ->
  [ re Δ |- B.[ren (+1)].[σ] :- Sort L l ] ->
  [ re Γ |- B :- Sort L l ] ->
  [ Δ |- σ -| A +l Γ ] ->
  [ Δ |- σ -| B +l Γ ]
where "[ Δ |- σ -| Γ ]" := (agree_subst Δ σ Γ).

(** Various lemmas on agree_subst. *)

Lemma agree_subst_pure Δ σ Γ :
  [ Δ |- σ -| Γ ] -> pure Γ -> pure Δ.
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

Lemma agree_subst_refl Γ :
  [ Γ |- ids -| Γ ].
Proof.
  induction Γ.
  - constructor.
  - destruct a.
    destruct p.
    destruct s.
    replace [t +u Γ |- ids -| t +u Γ]
      with [t.[ids] +u Γ |- up ids -| t +u Γ]
      by autosubst.
    apply agree_subst_u; eauto.
    replace [t +l Γ |- ids -| t +l Γ]
      with [t.[ids] +l Γ |- up ids -| t +l Γ]
      by autosubst.
    apply agree_subst_l; eauto.
    replace (ids) with (up ids) by autosubst.
    apply agree_subst_n; eauto.
Qed.

Lemma agree_subst_hasU Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  forall x A,
    hasU Γ x A ->
    [ Δ |- σ x :- A.[σ] ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H0.
    + asimpl.
      apply u_var.
      replace (A.[σ >> ren (+1)]) 
        with (A.[σ].[ren (+1)]) by autosubst.
      constructor.
      eapply agree_subst_pure; eauto.
    + eapply eweakeningU; eauto; autosubst.
  - inv H0.
  - inv H0.
    eapply eweakeningN; eauto; autosubst.
  - inv H1; asimpl; eauto.
    pose proof (agree_subst_pure H H6).
    pose proof (pure_re H1).
    rewrite H2; eauto.
  - inv H2.
  - inv H0; asimpl; eauto.
  - inv H2.
    + assert (hasU (A +u Γ) 0 A.[ren (+1)]).
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

Lemma agree_subst_hasL Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  forall x A,
    hasL Γ x A ->
    [ Δ |- σ x :- A.[σ] ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H0.
    eapply eweakeningU; eauto; autosubst.
  - inv H0.
    asimpl.
    replace (A.[σ >> ren (+1)]) 
      with (A.[σ].[ren (+1)]) by autosubst.
    apply l_var.
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
    assert (hasL (A +l Γ) 0 A.[ren (+1)]).
    constructor; eauto.
    eapply conversion.
    apply sub_subst.
    apply sub_ren; eauto.
    apply H0.
    apply IHagree_subst; eauto.
Qed.

Lemma agree_subst_re_re Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  [ re Δ |- σ -| re Γ ].
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

(** When two contexts Δ and Γ agree on substition σ,
  if Γ could be split into two mergeable contexts Γ1 and Γ2,
  then there exists a way to split Δ into two mergeable
  contexts Δ1 and Δ2 such that Δ1 agrees with Γ1 on σ and
  Δ2 agrees with Γ2. Again, this is morally similar to the
  proof for weakening. *)

Lemma merge_agree_subst_inv Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  forall Γ1 Γ2,
    merge Γ1 Γ2 Γ ->
    exists Δ1 Δ2,
      merge Δ1 Δ2 Δ /\ [ Δ1 |- σ -| Γ1 ] /\ [ Δ2 |- σ -| Γ2 ].
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
    exists (A.[σ] +u x).
    exists (A.[σ] +u x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (A.[σ] +l x).
    exists (+n x0).
    repeat constructor; eauto.
  - pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (+n x).
    exists (A.[σ] +l x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (+n x).
    exists (+n x0).
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
    assert (merge (A +u Γ0) (A +u Γ3) (A +u Γ)).
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
    + assert (merge (A +l Γ0) (+n Γ3) (A +l Γ)).
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
    + assert (merge (+n Γ0) (A +l Γ3) (A +l Γ)).
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

(** The general substitution lemma. When contexts Δ and Γ agree on some
  generalized substitution σ, substituting σ uniformly for context,
  term and type yields a well-formed typing judgment. *)

Lemma substitution Γ m A :
  [ Γ |- m :- A ] ->
  forall Δ σ,
    [ Δ |- σ -| Γ ] ->
    [ Δ |- m.[σ] :- A.[σ] ].
Proof.
  intros H.
  dependent induction H; asimpl; intros; eauto.
  - apply s_axiom.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3).
    eapply u_arrow; simpl; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_n H2).
    specialize (IHhas_type2 _ _ H3).
    eapply l_arrow; simpl; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3).
    eapply u_lolli; simpl; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_n H2).
    specialize (IHhas_type2 _ _ H3).
    eapply l_lolli; simpl; eauto.
    eapply agree_subst_pure; eauto.
  - eapply agree_subst_hasU; eauto.
  - eapply agree_subst_hasL; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    destruct s.
    + pose proof (agree_subst_u A H2).
      specialize (IHhas_type2 _ _ H3).
      eapply arrow_lam; eauto.
      eapply agree_subst_pure; eauto.
    + pose proof (agree_subst_l A H2).
      specialize (IHhas_type2 _ _ H3).
      eapply arrow_lam; eauto.
      eapply agree_subst_pure; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    destruct s.
    + pose proof (agree_subst_u A H1).
      specialize (IHhas_type2 _ _ H3).
      eapply lolli_lam; eauto.
    + pose proof (agree_subst_l A H1).
      specialize (IHhas_type2 _ _ H3).
      eapply lolli_lam; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H3 H2).
    first_order.
    pose proof (agree_subst_pure H6 H).
    pose proof (u_arrow_app H7 IHhas_type1 IHhas_type2 H4).
    asimpl in H8; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    pose proof (l_arrow_app IHhas_type1 IHhas_type2 H3).
    asimpl in H6; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H3 H2).
    first_order.
    pose proof (agree_subst_pure H6 H).
    pose proof (u_lolli_app H7 IHhas_type1 IHhas_type2 H4).
    asimpl in H8; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    pose proof (l_lolli_app IHhas_type1 IHhas_type2 H3).
    asimpl in H6; eauto.
  - eapply conversion.
    apply sub_subst; eauto.
    apply IHhas_type1; eauto.
    apply agree_subst_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

(** Specialization of the general substitution lemma to a single
  non-linear variable. *)

Lemma substitutionU Γ1 m A B :
  [ A +u Γ1 |- m :- B ] ->
  forall Γ2 Γ n,
    pure Γ2 ->
    merge Γ1 Γ2 Γ -> 
    [ Γ2 |- n :- A ] -> 
    [ Γ |- m.[n/] :- B.[n/] ].
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

(** Specialization of the general substitution lemma to a single
  empty context slot. *)

Lemma substitutionN Γ1 m A B :
  [ +n Γ1 |- m :- B ] ->
  forall Γ2 n,
    [ Γ2 |- n :- A ] -> 
    [ Γ1 |- m.[n/] :- B.[n/] ].
Proof.
  intros.
  eapply substitution.
  apply H.
  apply agree_subst_wkN; eauto.
  apply agree_subst_refl.
Qed.

(** Specialization of the general substitution lemma to a single
  linear variable. *)

Lemma substitutionL Γ1 m A B :
  [ A +l Γ1 |- m :- B ] ->
  forall Γ2 Γ n,
    merge Γ1 Γ2 Γ -> 
    [ Γ2 |- n :- A ] -> 
    [ Γ |- m.[n/] :- B.[n/] ].
Proof.
  intros.
  eapply substitution.
  apply H.
  eapply agree_subst_wkL; asimpl; eauto.
  apply agree_subst_refl.
Qed.

(** Context conversions is now derivable as a corollary of substitution. *)

Lemma context_convU Γ m A B C l :
  B === A -> 
  [ re Γ |- A :- U @ l ] ->
  [ A +u Γ |- m :- C ] -> 
  [ B +u Γ |- m :- C ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B +u Γ |- m.[ids] :- C.[ids] ]). autosubst.
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

Lemma context_convL Γ m A B C l :
  B === A -> 
  [ re Γ |- A :- L @ l ] ->
  [ A +l Γ |- m :- C ] -> 
  [ B +l Γ |- m :- C ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B +l Γ |- m.[ids] :- C.[ids] ]). autosubst.
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