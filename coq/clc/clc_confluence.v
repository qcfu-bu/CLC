From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS clc_context clc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Confluence Property of CLC 

    The confluence of CLC reductions is proven through the parallel
    reduction proof techique. *)

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort srt l :
  pstep (Sort srt l) (Sort srt l)
| pstep_lam A A' n n' s : 
  pstep A A' -> 
  pstep n n' -> 
  pstep (Lam A n s) (Lam A' n' s)
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta A m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam A m s) n) (m'.[n'/])
| pstep_arrow A A' s B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Arrow A B s) 
        (Arrow A' B' s)
| pstep_lolli A A' s B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Lolli A B s) 
        (Lolli A' B' s).

Definition sred σ τ :=
  forall x : var, (σ x) ~>* (τ x).

Lemma step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ => /={m n}; eauto using step.
  move=> A m n s σ. 
  replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
  apply step_beta. autosubst.
Qed.

Lemma red_app m1 m2 n1 n2 :
  m1 ~>* m2 -> n1 ~>* n2 -> (App m1 n1) ~>* (App m2 n2).
Proof.
  move=> A B. apply: (star_trans (App m2 n1)).
  - apply: (star_hom (App^~ n1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_lam A1 A2 m1 m2 s : 
  A1 ~>* A2 -> m1 ~>* m2 -> Lam A1 m1 s ~>* Lam A2 m2 s.
Proof. 
  move=> A B. apply: (star_trans (Lam A2 m1 s)).
  - apply: (star_hom ((Lam^~ m1)^~ s)) A => x y. exact: step_lamL.
  - apply: (star_hom ((Lam A2)^~ s)) B => x y. exact: step_lamR.
Qed.

Lemma red_arrow A1 A2 B1 B2 s :
  A1 ~>* A2 -> B1 ~>* B2 -> Arrow A1 B1 s ~>* Arrow A2 B2 s.
Proof.
  move=> A B. apply: (star_trans (Arrow A2 B1 s)).
  - apply: (star_hom ((Arrow^~ B1)^~ s)) A => x y. exact: step_arrowL.
  - apply: (star_hom ((Arrow A2)^~ s)) B => x y. exact: step_arrowR.
Qed.

Lemma red_lolli A1 A2 B1 B2 s :
  A1 ~>* A2 -> B1 ~>* B2 -> Lolli A1 B1 s ~>* Lolli A2 B2 s.
Proof.
  move=> A B. apply: (star_trans (Lolli A2 B1 s)).
  - apply: (star_hom ((Lolli^~ B1)^~ s)) A => x y. exact: step_lolliL.
  - apply: (star_hom ((Lolli A2)^~ s)) B => x y. exact: step_lolliR.
Qed.

Lemma red_subst m n : 
  m ~>* n -> forall σ, m.[σ] ~>* n.[σ].
Proof.
  induction 1; intros.
  eauto.
  eapply star_trans.
  apply IHstar; eauto.
  econstructor; eauto.
  apply step_subst; eauto.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: red_subst. exact: A. Qed.

Hint Resolve red_app red_lam red_arrow red_lolli sred_up : red_congr.

Lemma red_compat σ τ s : sred σ τ -> red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with red_congr. Qed.

Definition sconv (σ τ : var -> term) :=
  forall x, σ x === τ x.

Lemma conv_lam A1 A2 m1 m2 s : 
  A1 === A2 -> m1 === m2 -> Lam A1 m1 s === Lam A2 m2 s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Lam A2 m1 s)).
  - apply: (conv_hom ((Lam^~ m1)^~ s)) conv1 => x y ps.
    constructor; eauto.
  - apply: (conv_hom ((Lam A2)^~ s)) conv2 => x y ps.
    constructor; eauto.
Qed.

Lemma conv_arrow A A' s B B' :
  A === A' -> B === B' -> Arrow A B s === Arrow A' B' s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Arrow A' B s)).
  - apply: (conv_hom ((Arrow^~ B)^~ s)) conv1 => x y ps.
    constructor; eauto.
  - apply: (conv_hom ((Arrow A')^~ s)) conv2 => x y ps.
    constructor; eauto.
Qed.

Lemma conv_lolli A A' s B B' :
  A === A' -> B === B' -> Lolli A B s === Lolli A' B' s.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Lolli A' B s)).
  - apply: (conv_hom ((Lolli^~ B)^~ s)) conv1 => x y ps.
    constructor; eauto.
  - apply: (conv_hom ((Lolli A')^~ s)) conv2 => x y ps.
    constructor; eauto.
Qed.

Lemma conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> A B. apply: (conv_trans (App m' n)).
  - apply: (conv_hom (App^~ n)) A => x y ps. 
    constructor; eauto.
  - apply: conv_hom B => x y ps.
    constructor; eauto.
Qed.

Lemma conv_subst σ s t : 
  s === t -> s.[σ] === t.[σ].
Proof. 
  intro H.
  eapply conv_hom; eauto.
  intros.
  apply step_subst; eauto.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Lemma conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof.
  elim: s σ τ => *; asimpl; eauto using
    conv_app, conv_lam, conv_arrow, conv_lolli, sconv_up.
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep n n' : step n n' -> pstep n n'.
Proof with eauto using pstep, pstep_refl.
  intros.
  induction H...
Qed.

Lemma pstep_red s t : pstep s t -> s ~>* t.
Proof.
  elim=> {s t} //=; eauto with red_congr.
  move=> A m m' n n' s p1 r1 p2 r2. eapply starES. by econstructor.
  apply: (star_trans (m'.[n.:Var])). exact: red_subst.
  by apply: red_compat => -[|].
Qed.

Lemma pstep_subst s t : 
  pstep s t -> 
    forall σ, pstep s.[σ] t.[σ].
Proof with eauto using pstep, pstep_refl.
  intros.
  dependent induction H...
  - asimpl.
    specialize (IHpstep1 (up σ)).
    specialize (IHpstep2 σ).
    pose proof (pstep_beta A.[σ] s IHpstep1 IHpstep2).
    asimpl in H1; eauto.
Qed.

Definition psstep (σ τ : var -> term) := 
  forall x, pstep (σ x) (τ x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl.
  unfold psstep.
  induction x...
Qed.

Lemma psstep_up σ τ :
  psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat s t :
  pstep s t ->
  forall σ τ, 
    psstep σ τ -> pstep s.[σ] t.[τ].
Proof with eauto 6 using pstep, psstep_up.
  intros.
  dependent induction H; asimpl...
  - pose proof (psstep_up H1).
    pose proof (IHpstep1 _ _ H2).
    pose proof (IHpstep2 _ _ H1).
    pose proof (pstep_beta A.[σ] s H3 H4).
    asimpl in H5; eauto.
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep, pstep_refl.
  intros.
  apply pstep_compat...
  - apply psstep_compat...
    apply psstep_refl.
Qed.

Lemma pstep_compat_beta m m' :
  pstep m m' -> 
  forall n n',
    pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using psstep_refl, psstep_compat.
  intros.
  apply pstep_compat...
Qed.

Ltac first_order :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : ex2 _ _ |- _ ] => destruct H
  | [ H1 : ?A -> _, H2 : ?A |- _ ] => specialize (H1 H2)
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ |- _ /\ _ ] => split
  end.

(** Differ standard method of using rho triangle to prove parallel 
    reduction possessing the diamond property, we prove the
    diamond property directly by induction. *)

Lemma pstep_diamond m m1 :
  pstep m m1 ->
  forall m2, pstep m m2 ->
    exists m', pstep m1 m' /\ pstep m2 m'.
Proof with eauto using pstep, pstep_refl.
  intros.
  dependent induction H.
  - inv H0. exists (Var x)...
  - inv H0. exists (Sort srt l)...
  - inv H1. 
    apply (IHpstep1) in H6. apply (IHpstep2) in H7. first_order.
    exists (Lam x0 x s)...
  - inv H1.
    + apply (IHpstep1) in H4. apply (IHpstep2) in H6. first_order.
      exists (App x0 x)...
    + inv H. 
      assert (pstep (Lam A m0 s) (Lam A' m'0 s))...
      apply (IHpstep1) in H.  apply (IHpstep2) in H6. first_order.
      inv H.
      inv H2.
      exists (n'2.[x0/]). split.
      apply pstep_beta...
      apply pstep_compat_beta...
  - inv H1.
    + inv H4.
      apply IHpstep1 in H8. apply IHpstep2 in H6. first_order.
      exists (x.[x0/]). split.
      * apply pstep_compat_beta...
      * apply pstep_beta...
    + apply IHpstep1 in H7. apply IHpstep2 in H8. first_order.
      exists (x0.[x/]). split.
      * apply pstep_compat_beta...
      * apply pstep_compat_beta...
  - inv H1. apply (IHpstep1) in H6. apply (IHpstep2) in H7.
    first_order. exists (Arrow x0 x s)...
  - inv H1. apply (IHpstep1) in H6. apply (IHpstep2) in H7.
    first_order. exists (Lolli x0 x s)...
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> red m m2 ->
    exists m', red m1 m' /\ pstep m2 m'.
Proof with eauto using pstep_refl, star.
  intros.
  dependent induction H0... first_order.
  pose proof (step_pstep H1).
  pose proof (pstep_diamond H4 H3). first_order.
  exists x0. split...
  eapply star_trans; eauto.
  apply pstep_red; eauto.
Qed.

(** Using the diamond property of parallel reductions, we can 
    prove that CLC has confluence. *)

Theorem confluence :
  confluent step.
Proof with eauto using step, star.
  unfold confluent.
  unfold joinable.
  intros.
  dependent induction H.
  - exists z; eauto.
  - first_order.
    apply step_pstep in H0.
    pose proof (strip H0 H2). first_order.
    exists x1; eauto.
    eapply star_trans.
    apply H3.
    apply pstep_red; eauto.
Qed.
Hint Resolve confluence.

Theorem church_rosser :
  CR step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.
Hint Resolve church_rosser.

(** Various lemmas on renaming, reduction and conversion
  dervied from confluence. *)

Lemma red_sort_inv s l A :
  red (Sort s l) A -> A = (Sort s l).
Proof.
  induction 1; intros; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_arrow_inv A B s x :
  red (Arrow A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Arrow A' B' s.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order; subst.
    inv H0.
    + exists A'.
      exists x0.
      first_order; eauto.
      eapply star_trans; eauto.
      econstructor; eauto.
    + exists x.
      exists B'.
      first_order; eauto.
      eapply star_trans; eauto.
      econstructor; eauto.
Qed.

Lemma red_lolli_inv A B s x :
  red (Lolli A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Lolli A' B' s.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order; subst.
    inv H0.
    + exists A'.
      exists x0.
      first_order; eauto.
      eapply star_trans; eauto.
      econstructor; eauto.
    + exists x.
      exists B'.
      first_order; eauto.
      eapply star_trans; eauto.
      econstructor; eauto.
Qed.

Lemma red_var_inv x y :
  red (Var x) y -> y = Var x.
Proof.
  induction 1; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_lam_inv A m n s :
  red (Lam A m s) n ->
  exists A' m',
    red A A' /\ red m m' /\ n = Lam A' m' s.
Proof.
  induction 1.
  - exists A. exists m; repeat constructor.
  - first_order; subst.
    inv H0.
    exists A'. exists x0. repeat constructor; eauto using star.
    exists x. exists m'. repeat constructor; eauto using star.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  Sort s1 l1 === Sort s2 l2 ->
  s1 = s2 /\ l1 = l2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_sort_inv in H0.
  apply red_sort_inv in H1.
  first_order; subst; inv H1; eauto.
Qed.

Lemma arrow_inj A A' B B' s s' :
  Arrow A B s === Arrow A' B' s' ->
  A === A' /\ B === B' /\ s = s'.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_arrow_inv in H0.
  apply red_arrow_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
Qed.

Lemma lolli_inj A A' B B' s s' :
  Lolli A B s === Lolli A' B' s' ->
  A === A' /\ B === B' /\ s = s'.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_lolli_inv in H0.
  apply red_lolli_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
Qed.

(** Tactics for refuting obviously wrong conversions. *)

Ltac red_inv m H :=
  match m with
  | Var   => apply red_var_inv in H
  | Sort  => apply red_sort_inv in H
  | Arrow => apply red_arrow_inv in H
  | Lolli => apply red_lolli_inv in H
  | Lam   => apply red_lam_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : red (?m _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
  end;
  first_order; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  | [ H : value (App _ _) |- _ ] => inv H
  end; eauto.