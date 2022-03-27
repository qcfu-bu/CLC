From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** isL is a judgment asserting that variable x within
  context Γ has linear type. *)

Inductive isL : context term -> nat -> Prop :=
| isL_O Γ A :
  isL (A +l Γ) 0
| isL_S Γ i A s :
  isL Γ i ->
  isL (A +{s} Γ) i.+1
| isL_N Γ i :
  isL Γ i ->
  isL (+n Γ) i.+1.

(** isN is a judgment asserting that De Brujin indice x 
  within context Γ corresponds to an empty slot. *)

Inductive isN : context term -> nat -> Prop :=
| isN_O Γ :
  isN (+n Γ) 0
| isN_S Γ i A s :
  isN Γ i ->
  isN (A +{s} Γ) i.+1
| isN_N Γ i :
  isN Γ i ->
  isN (+n Γ) i.+1.

(** occurs is a function that counts the number of occurences
  a given variable appears within a term. *)

Fixpoint occurs (i : nat) (m : term) : nat :=
  match m with
  | Var x => if x == i then 1 else 0
  | Sort _ _ => 0
  | Arrow A B _ => occurs i A + occurs (i.+1) B
  | Lolli A B _ => occurs i A + occurs (i.+1) B
  | Lam A m _ => occurs i A + occurs (i.+1) m
  | App m n => occurs i m + occurs i n
  end.

Lemma eqn_refl (n : nat) : n == n.
Proof.
  induction n; simpl; eauto.
Qed.

Lemma isL_pure Γ i : isL Γ i -> ~pure Γ.
Proof.
  induction 1; unfold not; intros.
  inv H.
  destruct s.
  inv H0. firstorder.
  inv H0.
  inv H0. firstorder.
Qed.

Lemma isL_hasU Γ i : 
  isL Γ i -> forall x A, ~hasU Γ x A.
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

Lemma isL_hasL Γ i :
  isL Γ i -> forall x A, hasL Γ x A -> x = i.
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

Lemma isN_re Γ i : isN Γ i -> isN (re Γ) i.
Proof.
  induction 1; simpl; try constructor; eauto.
  destruct s; constructor; eauto.
Qed.

Lemma isL_isN Γ i : isL Γ i -> isN (re Γ) i.
Proof.
  induction 1; simpl; try constructor; eauto.
  destruct s; constructor; eauto.
Qed.

Lemma isN_hasU Γ i :
  isN Γ i -> forall x A, hasU Γ x A -> x == i = false.
Proof.
  induction 1; intros; eauto.
  inv H; eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H6); eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H2); eauto.
Qed.

Lemma isN_hasL Γ i :
  isN Γ i -> forall x A, hasL Γ x A -> x == i = false.
Proof.
  induction 1; intros; eauto.
  inv H; eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H6); eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H2); eauto.
Qed.

Lemma isL_merge_inv Γ1 Γ2 Γ :
  merge Γ1 Γ2 Γ -> 
    forall i, isL Γ i -> 
      (isL Γ1 i /\ isN Γ2 i) \/
      (isL Γ2 i /\ isN Γ1 i).
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

Lemma isN_merge_inv Γ1 Γ2 Γ :
  merge Γ1 Γ2 Γ -> 
    forall i, isN Γ i -> 
      isN Γ1 i /\ isN Γ2 i.
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

(** * Narity
  
  A variable that does not occur in the context of a 
  well-typed term does not occur in the term at all. *)

Lemma narity Γ m A :
  [ Γ |- m :- A ] -> 
    forall i, isN Γ i -> occurs i m = 0.
Proof.
  induction 1; simpl; intros.
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
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - pose proof (isN_hasU H0 H).
    rewrite H1; eauto.
  - pose proof (isN_hasL H0 H).
    rewrite H1; eauto.
  - pose proof (IHhas_type1 _ H2).
    simpl in H3.
    assert (occurs i A = 0).
    { destruct (occurs i.+1 B).
      rewrite addn0 in H3; eauto.
      destruct (occurs i A); discriminate. }
    rewrite H4.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - pose proof (isN_re H1).
    pose proof (IHhas_type1 _ H2).
    simpl in H3.
    assert (occurs i A = 0).
    { destruct (occurs i.+1 B).
      rewrite addn0 in H3; eauto.
      destruct (occurs i A); discriminate. }
    rewrite H4.
    rewrite IHhas_type2; eauto.
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

(** * Linearity

  For a well-typed term, linear variables in the context
  occurs exactly once within the term itself. *)

Theorem linearity Γ m A :
  [ Γ |- m :- A ] -> 
    forall i, isL Γ i -> occurs i m = 1.
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
  - simpl.
    pose proof (isL_isN H1).
    eapply narity in H; eauto.
    simpl in H.
    assert (occurs i A = 0).
    { destruct (occurs i.+1 B).
      rewrite addn0 in H; eauto.
      destruct (occurs i A); discriminate. }
    rewrite H3.
    rewrite IHhas_type2; eauto.
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

(** * Promotion 

  A well-typed linear function under a pure context can
  be promoted to a non-linear function using eta-expansion. *)

Theorem promotion Γ m A B s :
  pure Γ ->
  [ Γ |- ] ->
  [ Γ |- m :- Lolli A B s ] ->
  exists m, [ Γ |- m :- Arrow A B s ].
Proof.
  intros.
  exists (Lam A (App m.[ren (+1)] (Var 0)) s).
  destruct s.
  - pose proof (validity H0 H1); first_order. 
    apply u_lolli_inv in H2; first_order.
    assert ([ Γ |- Arrow A B U :- Sort U x2 ]).
    eapply u_arrow; eauto.
    rewrite <- pure_re in H2; eauto.
    rewrite <- pure_re in H3; eauto.
    eapply arrow_lam; eauto.
    assert (hasU (A +u Γ) 0 A.[ren (+1)]).
    apply hasU_O; eauto.
    assert ([ A +u Γ |- Var 0 :- A.[ren (+1)] ]).
    eapply u_var; eauto.
    pose proof (weakeningU A H1).
    asimpl in H7.
    assert (pure (A +u Γ)).
    constructor; eauto.
    assert (merge (A +u Γ) (A +u Γ) (A +u Γ)).
    apply merge_pure; eauto.
    pose proof (u_lolli_app H8 H7 H6 H9).
    asimpl in H10; eauto.
  - pose proof (validity H0 H1); first_order. 
    apply l_lolli_inv in H2; first_order.
    assert ([ Γ |- Arrow A B L :- Sort U x2 ]).
    eapply l_arrow; eauto.
    rewrite <- pure_re in H2; eauto.
    rewrite <- pure_re in H3; eauto.
    eapply arrow_lam; eauto.
    assert (hasL (A +l Γ) 0 A.[ren (+1)]).
    apply hasL_O; eauto.
    assert ([ A +l Γ |- Var 0 :- A.[ren (+1)] ]).
    eapply l_var; eauto.
    pose proof (weakeningN H1).
    asimpl in H7.
    assert (merge (+n Γ) (A +l Γ) (A +l Γ)).
    constructor.
    apply merge_pure; eauto.
    pose proof (l_lolli_app H7 H6 H8).
    asimpl in H9; eauto.
Qed.

(** * Promotion 

  A well-typed non-linear function can be used in-place of a
  linear function using eta-expansion. *)
  
Theorem dereliction Γ m A B s :
  [ Γ |- ] ->
  [ Γ |- m :- Arrow A B s ] ->
  exists m, [ Γ |- m :- Lolli A B s ].
Proof.
  intros.
  exists (Lam A (App m.[ren (+1)] (Var 0)) s).
  destruct s.
  - pose proof (validity H H0); first_order. 
    apply u_arrow_inv in H1; first_order.
    destruct x1.
    + assert ([ re Γ |- Lolli A B U :- L @ x2 ]).
      eapply u_lolli; eauto.
      apply re_pure.
      eapply lolli_lam; eauto.
      assert (hasU (A +u re Γ) 0 A.[ren (+1)]).
      apply hasU_O.
      apply re_pure.
      assert ([ A +u re Γ |- Var 0 :- A.[ren (+1)] ]).
      eapply u_var; eauto.
      pose proof (weakeningU A H0).
      asimpl in H6.
      assert (pure (A +u re Γ)).
      constructor; eauto.
      apply re_pure.
      assert (merge (A +u Γ) (A +u re Γ) (A +u Γ)).
      constructor.
      apply merge_re2.
      pose proof (u_arrow_app H7 H6 H5 H8).
      asimpl in H9; eauto.
    + assert ([ re Γ |- Lolli A B U :- L @ x2 ]).
      eapply u_lolli; eauto.
      apply re_pure.
      eapply lolli_lam; eauto.
      assert (hasU (A +u re Γ) 0 A.[ren (+1)]).
      apply hasU_O.
      apply re_pure.
      assert ([ A +u re Γ |- Var 0 :- A.[ren (+1)] ]).
      eapply u_var; eauto.
      pose proof (weakeningU A H0).
      asimpl in H6.
      assert (pure (A +u re Γ)).
      constructor; eauto.
      apply re_pure.
      assert (merge (A +u Γ) (A +u re Γ) (A +u Γ)).
      constructor.
      apply merge_re2.
      pose proof (u_arrow_app H7 H6 H5 H8).
      asimpl in H9; eauto.
  - pose proof (validity H H0); first_order. 
    apply l_arrow_inv in H1; first_order.
    destruct x1.
    + assert ([ re Γ |- Lolli A B L :- L @ x2 ]).
      eapply l_lolli; eauto.
      apply re_pure.
      eapply lolli_lam; eauto.
      assert (hasL (A +l re Γ) 0 A.[ren (+1)]).
      apply hasL_O.
      apply re_pure.
      assert ([ A +l re Γ |- Var 0 :- A.[ren (+1)] ]).
      eapply l_var; eauto.
      pose proof (weakeningN H0).
      asimpl in H6.
      assert (merge (+n Γ) (A +l re Γ) (A +l Γ)).
      constructor.
      apply merge_re2.
      pose proof (l_arrow_app).
      pose proof (l_arrow_app H6 H5 H7).
      asimpl in H9; eauto.
    + assert ([ re Γ |- Lolli A B L :- L @ x2 ]).
      eapply l_lolli; eauto.
      apply re_pure.
      eapply lolli_lam; eauto.
      assert (hasL (A +l re Γ) 0 A.[ren (+1)]).
      apply hasL_O.
      apply re_pure.
      assert ([ A +l re Γ |- Var 0 :- A.[ren (+1)] ]).
      eapply l_var; eauto.
      pose proof (weakeningN H0).
      asimpl in H6.
      assert (merge (+n Γ) (A +l re Γ) (A +l Γ)).
      constructor.
      apply merge_re2.
      pose proof (l_arrow_app H6 H5 H7).
      asimpl in H8; eauto.
Qed.