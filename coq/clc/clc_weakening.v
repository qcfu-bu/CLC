From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Weakening for the Non-linear Fragment of CLC 
  
  Weaknening for non-linear types is admissible in CLC.
  To prove this, we first define an agree_ren ξ Γ Γ' judgment
  that relates two contexts Γ and Γ' if Γ' can be obtained
  by some renaming Γ using ξ. *)

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_u Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m +u Γ) (m.[ren ξ] +u Γ')
| agree_ren_l Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m +l Γ) (m.[ren ξ] +l Γ')
| agree_ren_n Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (□ Γ) (□ Γ')
| agree_ren_wkU Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) (Γ) (m +u Γ')
| agree_ren_wkN Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) (Γ) (□ Γ').

(** Various basic lemmas on agree_ren. *)

Lemma agree_ren_refl Γ :
  agree_ren id Γ Γ.
Proof.
  induction Γ.
  - constructor.
  - destruct a. 
    destruct p.
    destruct s.
    assert (agree_ren id (t +u Γ) (t +u Γ)
      = agree_ren (upren id) (t +u Γ) (t.[ren id] +u Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (t +l Γ) (t +l Γ)
      = agree_ren (upren id) (t +l Γ) (t.[ren id] +l Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (□ Γ) (□ Γ)
      = agree_ren (upren id) (□ Γ) (□ Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
Qed.

Lemma agree_ren_pure Γ Γ' ξ :
  agree_ren ξ Γ Γ' -> [ Γ ] -> [ Γ' ].
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

Lemma agree_ren_re_re Γ Γ' ξ :
  agree_ren ξ Γ Γ' -> agree_ren ξ (%Γ) (%Γ').
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma agree_ren_hasU Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  forall x A,
    [ x :u A ∈ Γ ]  ->
    [ ξ x :u A.[ren ξ] ∈ Γ' ].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    eapply agree_ren_pure; eauto.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren ξ)]) 
      with (m0.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H.
  - inv H; subst.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
Qed.

Lemma agree_ren_hasL Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  forall x A,
    [ x :l A ∈ Γ ] ->
    [ ξ x :l A.[ren ξ] ∈ Γ' ].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren ξ)]) 
      with (m0.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    eapply agree_ren_pure; eauto.
  - inv H.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
Qed.

(** merge_agree_ren_inv states that if two contexts Γ and Γ'
  agree under renaming ξ, then for all ways Γ can be split
  into mergeable contexts Γ1 and Γ2, there exists a way to
  split Γ' into Γ1' and Γ2' such that Γ1 agrees with Γ1' on ξ
  and Γ2 agrees with Γ2' on ξ. 
 
  This lemma is used in the application case to split the context
  obtained by merging the function context and argument context. *)

Lemma merge_agree_ren_inv Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  forall Γ1 Γ2,
    [ Γ1 ‡ Γ2 ‡ Γ ] ->
    exists Γ1' Γ2',
      [ Γ1' ‡ Γ2' ‡ Γ' ] /\
      agree_ren ξ Γ1 Γ1' /\
      agree_ren ξ Γ2 Γ2'.
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    exists nil.
    repeat constructor.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren ξ] +u x).
    exists (m.[ren ξ] +u x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren ξ] +l x).
    exists (□ x0).
    repeat constructor; eauto.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (□ x).
    exists (m.[ren ξ] +l x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (□ x).
    exists (□ x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (m +u x).
    exists (m +u x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (□ x).
    exists (□ x0).
    repeat constructor; eauto.
Qed.

(** If two contexts Γ and Γ' agree on renaming ξ, 
  then uniformingly renaming context, term and type yeilds
  a well-formed typing judgment. *)

Lemma rename_ok Γ m A :
  [ Γ |- m :- A ] ->
  forall Γ' ξ,
    agree_ren ξ Γ Γ' ->
    [ Γ' |- m.[ren ξ] :- A.[ren ξ] ].
Proof.
  intros H.
  induction H; simpl; intros.
  - pose proof (agree_ren_pure H0 H).
    apply p_axiom; assumption.
  - pose proof (agree_ren_pure H0 H).
    apply s_axiom; assumption.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply prop; eauto.
    replace 𝐏 with (𝐏.[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply u_prod; eauto.
    replace (s @ l) with ((s @ l).[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply l_prod; eauto.
    replace (s @ l) with ((s @ l).[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply u_lolli; eauto.
    replace (s @ l) with ((s @ l).[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply l_lolli; eauto.
    replace (s @ l) with ((s @ l).[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - replace (ids (ξ x)) with (Var (ξ x)) by autosubst.
    apply u_var.
    eapply agree_ren_hasU; eauto.
  - replace (ids (ξ x)) with (Var (ξ x)) by autosubst.
    apply l_var.
    eapply agree_ren_hasL; eauto.
  - eapply prod_lam.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    asimpl.
    apply IHhas_type2; eauto.
    destruct s; constructor; eauto.
  - eapply lolli_lam.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    asimpl.
    apply IHhas_type2.
    destruct s; constructor; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H3 H2).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    pose proof (agree_ren_pure H6 H).
    eapply u_prod_app; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    eapply l_prod_app; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H3 H2).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    pose proof (agree_ren_pure H6 H).
    eapply u_lolli_app; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    eapply l_lolli_app; eauto.
  - eapply conversion.
    apply sub_ren; eauto.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma hasU_ok Γ :
  [ Γ |- ] ->
  forall x A,
    [ x :u A ∈ Γ ] ->
    exists l, [ %Γ |- A :- Sort U l ].
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

Lemma hasL_ok Γ :
  [ Γ |- ] ->
  forall x A,
    [ x :l A ∈ Γ ] ->
    exists l, [ %Γ |- A :- Sort L l ].
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

(** Weakening for non-linear variables can be derived as a corollary
  of renaming. *)

Lemma weakeningU Γ m A B :
  [ Γ |- m :- A ] ->
  [ B +u Γ |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkU.
  apply agree_ren_refl.
Qed.

(** Adding empty De Brujin slots in the context is also admissible. *)

Lemma weakeningN Γ m A :
  [ Γ |- m :- A ] ->
  [ □ Γ |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkN.
  apply agree_ren_refl.
Qed.

Lemma eweakeningU Γ m m' A A' B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Γ |- m :- A ] -> 
  [ B +u Γ |- m' :- A' ].
Proof.  
  intros; subst.
  apply weakeningU; eauto.
Qed.

Lemma eweakeningN Γ m m' A A' :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Γ |- m :- A ] -> 
  [ □ Γ |-m' :- A' ].
Proof.  
  intros; subst.
  apply weakeningN; eauto.
Qed.