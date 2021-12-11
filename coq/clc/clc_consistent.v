From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_linearity.
Require Import cc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Consistency of CLC 

  The consistency of CLC can be proven as an erasure of CLC into
  CCω which is known to be consistent. Erasure of linear annotations
  in well-typed CLC terms yield well-type CCω terms. Erasure also
  preserves reduction, so strong normalization of CLC can be proved 
  in a straightforward manner. *)

Fixpoint erase (m : clc_ast.term) : term :=
  match m with
  | clc_ast.Var x => Var x
  | clc_ast.Sort _ l => Sort l
  | clc_ast.Arrow A B _ => Arrow (erase A) (erase B)
  | clc_ast.Lolli A B _ => Arrow (erase A) (erase B)
  | clc_ast.Lam A n s => Lam (erase A) (erase n)
  | clc_ast.App m n => App (erase m) (erase n)
  end.

Fixpoint erase_context 
  (Γ : clc_context.context clc_ast.term) 
: context term :=
  match Γ with
  | Some (t, U) :: Γ => erase t +: erase_context Γ
  | Some (t, L) :: Γ => erase t +: erase_context Γ
  | None :: Γ => □ erase_context Γ
  | nil => nil
  end.

Notation "[| m |]" := (erase m).
Notation "[[ Γ ]]" := (erase_context Γ).

Lemma erase_value v : 
  clc_ast.value v <-> value [|v|].
Proof.
  split.
  induction 1; simpl; constructor.
  induction v; simpl; try constructor.
  intros.
  inv H.
Qed.

Definition erase_subst 
  (σ : var -> clc_ast.term) 
  (τ : var -> term)
: Prop := 
  forall x, [|σ x|] = τ x.

Lemma erase_ren_com m :
  forall ξ, [| m |].[ren ξ] = [| m.[ren ξ] |].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm1 IHm2; eauto.
Qed.

Lemma erase_subst_up σ τ :
  erase_subst σ τ -> erase_subst (up σ) (up τ).
Proof.
  unfold erase_subst.
  intros.
  induction x; asimpl; eauto.
  rewrite <-H.
  rewrite erase_ren_com; eauto.
Qed.

Lemma erase_subst_com m :
  forall σ τ, 
    erase_subst σ τ ->
    [| m.[σ] |] = [| m |].[τ].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite <- (IHm σ); eauto.
    rewrite <- (IHm0 (up σ)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm σ); eauto.
    rewrite <- (IHm0 (up σ)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm σ); eauto.
    rewrite <- (IHm0 (up σ)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm1 σ); eauto.
    rewrite <- (IHm2 σ); eauto.
Qed.

Lemma erase_step m n :
  clc_ast.step m n -> step [|m|] [|n|].
Proof with eauto using step.
  induction 1; simpl; intros...
  erewrite erase_subst_com.
  eapply step_beta; eauto.
  unfold erase_subst; intros; destruct x; asimpl; eauto.
Qed.

Lemma erase_red m n :
  clc_ast.red m n -> red [|m|] [|n|].
Proof with eauto using step, star.
  induction 1; simpl; intros...
  apply erase_step in H0.
  apply star1 in H0.
  eapply star_trans; eauto.
Qed.

Lemma erase_conv m n :
  conv clc_ast.step m n -> conv step [|m|] [|n|].
Proof.
  induction 1; eauto.
  eapply conv_trans.
  apply IHconv.
  eapply convSE; eauto.
  apply erase_step; eauto.
  eapply convSEi; eauto.
  apply erase_step; eauto.
Qed.

Lemma erase_sub1 m n :
  clc_subtype.sub1 m n -> sub1 [|m|] [|n|].
Proof.
  induction 1; asimpl; eauto using sub1.
Qed.

Lemma erase_sub m n :
  clc_subtype.sub m n -> sub [|m|] [|n|].
Proof.
  move=> [A B sb] c1 c2.
  inv sb.
  - assert (conv clc_ast.step m n).
    eapply conv_trans.
    apply c1.
    apply c2.
    apply erase_conv in H.
    apply conv_sub; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    assert (sub1 𝐏 (𝐔 l)).
    constructor; eauto.
    apply sub1_sub in H.
    eapply sub_trans. eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    assert (sub1 (𝐔 l1) (𝐔 l2)).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert (sub1 (Arrow [|A0|] [|B1|]) (Arrow [|A0|] [|B2|])).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert (sub1 (Arrow [|A0|] [|B1|]) (Arrow [|A0|] [|B2|])).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma hasU_erase Γ x A :
  [ x :u A ∈ Γ ] -> [ x :- [| A |] ∈ [[ Γ ]] ].
Proof.
  intros.
  dependent induction H; asimpl; firstorder;
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Lemma hasL_erase Γ x A :
  [ x :l A ∈ Γ ] -> [ x :- [| A |] ∈ [[ Γ ]] ].
Proof.
  intros.
  dependent induction H; asimpl; firstorder;
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Inductive agree_wk : 
  context term -> context term -> Prop :=
| agree_wk_nil : agree_wk nil nil
| agree_wk_s Γ1 Γ2 e :
  agree_wk Γ1 Γ2 ->
  agree_wk (e :: Γ1) (e :: Γ2)
| agree_wk_n Γ1 Γ2 A :
  agree_wk Γ1 Γ2 ->
  agree_wk (□ Γ1) (A +: Γ2).

Lemma agree_wk_refl Γ : agree_wk Γ Γ.
Proof.
  induction Γ.
  - constructor.
  - constructor; eauto.
Qed.

Lemma agree_wk_has Γ1 Γ2 :
  agree_wk Γ1 Γ2 ->
  forall x A,
    [ x :- A ∈ Γ1 ] -> 
    [ x :- A ∈ Γ2 ].
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  inv H0; constructor; eauto.
  inv H0; constructor; eauto.
Qed.

Lemma agree_wk_re Γ :
  agree_wk [[ %Γ ]] [[ Γ ]].
Proof.
  induction Γ.
  - simpl; constructor.
  - destruct a. 
    destruct p.
    destruct s; simpl; constructor; eauto.
    constructor; eauto.
Qed.

Lemma agree_wk_merge_inv Γ1 Γ2 Γ :
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  agree_wk [[ Γ1 ]] [[ Γ ]] /\
  agree_wk [[ Γ2 ]] [[ Γ ]].
Proof with eauto using agree_wk.
  intro H.
  dependent induction H; simpl; firstorder...
Qed.

Lemma wk_ok Γ1 m A : 
  [ Γ1 |- m :- A ] ->
  forall Γ2, agree_wk Γ1 Γ2 ->
    [ Γ2 |- m :- A ].
Proof.
  intro H.
  dependent induction H; simpl; intros; subst.
  - apply p_axiom.
  - apply t_axiom.
  - eapply ty_prop; eauto.
    apply IHhas_type2; constructor; eauto.
  - apply ty_arrow.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - pose proof (agree_wk_has H0 H).
    apply ty_var; eauto.
  - eapply ty_lam.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_app.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
  - eapply ty_conv.
    apply H.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma erase_re Γ m A :
  [ [[ %Γ ]] |- m :- A ] ->
  [ [[ Γ ]] |- m :- A ].
Proof.
  intro H.
  eapply wk_ok; eauto.
  apply agree_wk_re.
Qed.

Lemma erase_subst_trivial n :
  erase_subst (n .: ids) ([| n |] .: ids).
Proof.
  unfold erase_subst; intros.
  destruct x; simpl; eauto.
Qed.

Theorem embedding Γ m A : 
  clc_typing.has_type Γ m A ->
  has_type [[ Γ ]] [| m |] [| A |].
Proof.
  intro H.
  dependent induction H; asimpl.
  - apply p_axiom.  
  - apply t_axiom.  
  - eapply ty_prop; eauto.
  - apply ty_arrow; eauto.
  - apply ty_arrow; eauto.
    eapply wk_ok; eauto; simpl.
    constructor.
    apply agree_wk_refl.
  - apply ty_arrow; eauto.
  - apply ty_arrow; eauto.
    eapply wk_ok; eauto; simpl.
    constructor.
    apply agree_wk_refl.
  - apply hasU_erase in H.
    apply ty_var; eauto.
  - apply hasL_erase in H.
    apply ty_var; eauto.
  - simpl in IHhas_type1.
    destruct s; simpl in IHhas_type2; eapply ty_lam; eauto.
  - simpl in IHhas_type1.
    destruct s; simpl in IHhas_type2. 
    + eapply ty_lam; eauto.
      apply erase_re; eauto.
    + eapply ty_lam; eauto.
      apply erase_re; eauto.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H2; destruct H2.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H1; destruct H1.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H2; destruct H2.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H1; destruct H1.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - eapply ty_conv.
    apply erase_sub; eauto.
    simpl in IHhas_type1.
    eapply wk_ok; eauto.
    apply agree_wk_re.
    apply IHhas_type2.
Qed.

Corollary embedding_context Γ :
  clc_typing.context_ok Γ -> [ [[Γ]] |- ].
Proof.
  induction 1; simpl. 
  constructor.
  apply embedding in H0.
  apply erase_re in H0.
  econstructor; eauto.
  apply embedding in H0.
  apply erase_re in H0.
  econstructor; eauto.
  constructor; eauto.
Qed.

Fixpoint lift (m : term) : clc_ast.term :=
  match m with
  | Var x => clc_ast.Var x
  | Sort n => clc_ast.Sort U n
  | App m n => clc_ast.App (lift m) (lift n)
  | Lam A m => clc_ast.Lam (lift A) (lift m) U
  | Arrow m n => clc_ast.Arrow (lift m) (lift n) U
  end.

Fixpoint lift_context
   (Γ : context term)
: clc_context.context clc_ast.term :=
  match Γ with
  | Some t :: Γ => lift t +u lift_context Γ
  | None :: Γ => □ lift_context Γ
  | nil => nil
  end.

Notation "{| m |}" := (lift m).
Notation "{{ Γ }}" := (lift_context Γ).

Lemma lift_pure Γ : [{{Γ}}].
Proof.
  induction Γ.
  constructor.
  destruct a; constructor; eauto.
Qed.

Definition lift_subst 
  (σ : var -> term) 
  (τ : var -> clc_ast.term)
: Prop := 
  forall x, {|σ x|} = τ x.

Lemma lift_ren_com m :
  forall ξ, {| m |}.[ren ξ] = {| m.[ren ξ] |}.
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite IHm1 IHm2; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm IHm0; eauto.
Qed.

Lemma lift_subst_up σ τ :
  lift_subst σ τ -> lift_subst (up σ) (up τ).
Proof.
  unfold lift_subst.
  intros.
  induction x; asimpl; eauto.
  rewrite <- lift_ren_com.
  rewrite H; eauto.
Qed.

Lemma lift_subst_com m :
forall σ τ, 
  lift_subst σ τ ->
  {| m.[σ] |} = {| m |}.[τ].
Proof.
  induction m; intros; asimpl; eauto.
  - erewrite IHm1; eauto.
    erewrite IHm2; eauto.
  - erewrite IHm; eauto.
    erewrite IHm0; eauto.
    apply lift_subst_up; eauto.
  - erewrite IHm; eauto.
    erewrite IHm0; eauto.
    apply lift_subst_up; eauto.
Qed.

Lemma lift_subst_trivial n :
  lift_subst (n .: ids) ({| n |} .: ids).
Proof.
  unfold lift_subst; intros.
  destruct x; simpl; eauto.
Qed.

Lemma lift_step m n :
  step m n -> clc_ast.step {|m|} {|n|}.
Proof with eauto using clc_ast.step.
  induction 1; simpl; intros...
  pose proof (lift_subst_trivial n).
  erewrite lift_subst_com; eauto.
  eapply clc_ast.step_beta; eauto.
Qed.

Lemma lift_red m n :
  red m n -> clc_ast.red {|m|} {|n|}.
Proof with eauto using clc_ast.step, star.
  induction 1; simpl; intros...
  apply lift_step in H0.
  apply star1 in H0.
  eapply star_trans; eauto.
Qed.

Lemma lift_conv m n :
  conv step m n -> conv clc_ast.step {|m|} {|n|}.
Proof.
  induction 1; eauto.
  eapply conv_trans.
  apply IHconv.
  eapply convSE; eauto.
  apply lift_step; eauto.
  eapply convSEi; eauto.
  apply lift_step; eauto.
Qed.

Lemma lift_sub1 m n :
  sub1 m n -> clc_subtype.sub1 {|m|} {|n|}.
Proof.
  induction 1; asimpl; eauto using clc_subtype.sub1.
Qed.

Lemma lift_sub m n :
  sub m n -> clc_subtype.sub {|m|} {|n|}.
Proof.
  move=> [A B sb] c1 c2.
  inv sb.
  - assert (conv step m n).
    eapply conv_trans.
    apply c1.
    apply c2.
    apply lift_conv in H.
    apply clc_subtype.conv_sub; eauto.
  - apply lift_conv in c1. simpl in c1.
    apply lift_conv in c2. simpl in c2.
    apply clc_subtype.conv_sub in c1.
    apply clc_subtype.conv_sub in c2.
    assert (clc_subtype.sub1 clc_typing.𝐏 (U @ l)).
    constructor; eauto.
    apply clc_subtype.sub1_sub in H.
    eapply clc_subtype.sub_trans. eauto.
    eapply clc_subtype.sub_trans; eauto.
  - apply lift_conv in c1. simpl in c1.
    apply lift_conv in c2. simpl in c2.
    apply clc_subtype.conv_sub in c1.
    apply clc_subtype.conv_sub in c2.
    assert (clc_subtype.sub1 (U @ l1) (U @ l2)).
    constructor; eauto.
    apply clc_subtype.sub1_sub in H0.
    eapply clc_subtype.sub_trans; eauto.
    eapply clc_subtype.sub_trans; eauto.
  - apply lift_conv in c1. simpl in c1.
    apply lift_conv in c2. simpl in c2.
    apply clc_subtype.conv_sub in c1.
    apply clc_subtype.conv_sub in c2.
    apply lift_sub1 in H.
    assert 
      (clc_subtype.sub1 
        (clc_ast.Arrow {|A0|} {|B1|} U) 
        (clc_ast.Arrow {|A0|} {|B2|} U)).
    constructor; eauto.
    apply clc_subtype.sub1_sub in H0.
    eapply clc_subtype.sub_trans; eauto.
    eapply clc_subtype.sub_trans; eauto.
Qed.

Lemma lift_hasU Γ x A :
  [ x :- A ∈ Γ ] -> [ x :u {|A|} ∈ {{Γ}} ].
Proof.
  intros.
  dependent induction H; simpl.
  - rewrite <- lift_ren_com.
    constructor.
    apply lift_pure.
  - rewrite <- lift_ren_com.
    constructor; eauto.
  - rewrite <- lift_ren_com.
    constructor; eauto.
Qed.

Theorem lifting Γ m A :
  has_type Γ m A -> 
  clc_typing.has_type {{ Γ }} {| m |} {| A |}.
Proof.
  intro H.
  dependent induction H; simpl.
  - constructor.
    apply lift_pure.
  - constructor.
    apply lift_pure.
  - econstructor; eauto.
    apply lift_pure.
  - econstructor; eauto.
    apply lift_pure.
  - econstructor; eauto.
    apply lift_hasU; eauto.
  - econstructor; eauto.
    apply lift_pure.
  - pose proof (lift_subst_trivial t).
    erewrite lift_subst_com; eauto.
    econstructor; eauto.
    apply lift_pure.
    apply merge_pure.
    apply lift_pure.
  - apply lift_sub in H.
    eapply clc_typing.conversion; eauto.
    rewrite <- pure_re; eauto.
    apply lift_pure.
Qed.

Corollary lifting_context Γ :
  context_ok Γ -> clc_typing.context_ok {{Γ}}.
Proof.
  induction 1; simpl. 
  constructor.
  apply lifting in H.
  econstructor; eauto.
  rewrite <- pure_re; eauto.
  apply lift_pure.
  econstructor; eauto.
Qed.

CoInductive nn T (Rel : T -> T -> Prop) : T -> Prop :=
| nnI m m' : Rel m m' -> nn Rel m' -> nn Rel m.

CoFixpoint erase_nn m : (nn clc_ast.step m) -> nn step [|m|].
Proof.
  intros.
  inv H.
  apply erase_step in H0.
  apply erase_nn in H1.
  econstructor; eauto.
Qed.

Lemma nn_sn T (Rel : T -> T -> Prop) m : nn Rel m -> ~sn Rel m.
Proof.
  move=> h1 h2. 
  induction h2.
  inv h1.
  eauto.
Qed.

Lemma not_sn T (Rel : T -> T -> Prop) m : 
  ~sn Rel m -> exists m', Rel m m' /\ ~sn Rel m'.
Proof.
  intros.
  pose proof (classic (exists m', Rel m m' /\ ~sn Rel m')).
  inv H0; eauto.
  - firstorder.
    simpl in H0.
    assert (forall n, Rel m n -> sn Rel n).
    intros.
    specialize (H0 n).
    apply not_and_or in H0.
    firstorder.
    apply NNPP; eauto.
    exfalso.
    eapply H.
    constructor; eauto.
Qed.

CoFixpoint sn_nn T (Rel : T -> T -> Prop) m : 
  ~sn Rel m -> nn Rel m.
Proof.
  move=> h. 
  apply not_sn in h.
  first_order.
  econstructor; eauto.
Qed.

Theorem strong_normalization Γ m A :
  clc_typing.has_type Γ m A -> (sn clc_ast.step m).
Proof.
  intros.
  pose proof (embedding H).
  pose proof (strong_normalization H0).
  pose proof (classic (nn clc_ast.step m)).
  inv H2.
  apply erase_nn in H3.
  exfalso; eapply nn_sn; eauto.
  pose proof (classic (sn clc_ast.step m)).
  inv H2; eauto.
  apply sn_nn in H4; exfalso; eauto.
Qed.