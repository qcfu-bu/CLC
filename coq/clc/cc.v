From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Logic.Classical_Prop.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The Standard Calulus of Constructions Omega. *)

Definition context T := seq (option T).

Notation "m +: Γ" := (Some m :: Γ) (at level 30).
Notation "□ Γ" := (None :: Γ) (at level 30).

Reserved Notation "[ x :- A ∈ Γ ]".
Inductive has {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| has_O m Γ :
  [ 0 :- m.[ren (+1)] ∈ m +: Γ ]
| has_S Γ v m n : 
  [ v :- m ∈ Γ ] ->
  [ v.+1 :- m.[ren (+1)] ∈ n +: Γ ]
| has_N Γ v m : 
  [ v :- m ∈ Γ ] ->
  [ v.+1 :- m.[ren (+1)] ∈ □ Γ ]
where "[ x :- A ∈ Γ ]" := (has Γ x A).

Lemma has_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ∈ Γ ] ->
  forall B,
    [ x :- B ∈ Γ ] -> A = B.
Proof.
  induction 1; intros.
  inv H1; eauto.
  inv H2; eauto.
  apply IHhas in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhas in H5. rewrite H5; eauto.
Qed.
  
Inductive term : Type :=
| Var   (x : var)
| Sort  (n : option nat)
| App   (s t : term)
| Lam   (s : term) (t : {bind term})
| Arrow (s : term) (t : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort l    : value (Sort l)
| value_var x     : value (Var x)
| value_arrow A B : value (Arrow A B)
| value_lam A n   : value (Lam A n).

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta A m n :
  (App (Lam A m) n) ~> m.[n/]
| step_lamL A A' m :
  A ~> A' ->
  Lam A m ~> Lam A' m
| step_lamR A m m' :
  m ~> m' ->
  Lam A m ~> Lam A m'
| step_arrowL A A' B :
  A ~> A' ->
  Arrow A B ~> Arrow A' B
| step_arrowR A B B' :
  B ~> B' ->
  Arrow A B ~> Arrow A B'
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
where "m ~> n" := (step m n).

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort n :
  pstep (Sort n) (Sort n)
| pstep_lam A1 A2 s1 s2 :
  pstep A1 A2 ->
  pstep s1 s2 ->
  pstep (Lam A1 s1) (Lam A2 s2)
| pstep_beta A s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (App (Lam A s1) t1) s2.[t2/]
| pstep_app s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (App s1 t1) (App s2 t2)
| pstep_arrow s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (Arrow s1 t1) (Arrow s2 t2).

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).

Definition sred σ τ :=
  forall x : var, (σ x) ~>* (τ x).

Lemma step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ => /={m n}; eauto using step.
  move=> A m n σ. 
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

Lemma red_lam A1 A2 s1 s2 : 
  A1 ~>* A2 -> s1 ~>* s2 -> Lam A1 s1 ~>* Lam A2 s2.
Proof. 
  move=> A B. apply: (star_trans (Lam A2 s1)).
  apply: (star_hom (Lam^~ s1)) A=> x y. exact: step_lamL.
  apply: (star_hom (Lam A2)) B=> x y. exact: step_lamR. 
Qed.

Lemma red_arrow A1 A2 B1 B2 :
  A1 ~>* A2 -> B1 ~>* B2 -> Arrow A1 B1 ~>* Arrow A2 B2.
Proof.
  move=> A B. apply: (star_trans (Arrow A2 B1)).
  - apply: (star_hom (Arrow^~ B1)) A => x y. exact: step_arrowL.
  - apply: (star_hom (Arrow A2)) B => x y. exact: step_arrowR.
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

Hint Resolve red_app red_lam red_arrow sred_up : red_congr.

Lemma red_compat σ τ s : sred σ τ -> red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with red_congr. Qed.

Definition sconv (σ τ : var -> term) :=
  forall x, σ x === τ x.

Lemma conv_lam A1 A2 m1 m2 : 
  A1 === A2 -> m1 === m2 -> Lam A1 m1 === Lam A2 m2.
Proof. 
  move=> A B.
  apply: (conv_trans (Lam A2 m1)).
  apply: (conv_hom (Lam^~ m1)) A=> x y. exact: step_lamL.
  apply: (conv_hom (Lam A2)) B=> x y. exact: step_lamR.
Qed.

Lemma conv_arrow A A' B B' :
  A === A' -> B === B' -> Arrow A B === Arrow A' B'.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Arrow A' B)).
  - apply: (conv_hom (Arrow^~ B)) conv1 => x y ps.
    constructor; eauto.
  - apply: (conv_hom (Arrow A')) conv2 => x y ps.
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
    conv_app, conv_lam, conv_arrow, sconv_up.
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Definition psstep (sigma tau : var -> term) :=
  forall x, pstep (sigma x) (tau x).

Fixpoint rho (s : term) : term :=
  match s with
  | App (Lam A s) t => (rho s).[rho t/]
  | App s t => App (rho s) (rho t)
  | Lam A s => Lam (rho A) (rho s)
  | Arrow A B => Arrow (rho A) (rho B)
  | x => x
  end.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof. elim; eauto using pstep. Qed.

Lemma pstep_red s t : pstep s t -> s ~>* t.
Proof.
  elim=> {s t} //=; eauto with red_congr.
  move=> A m m' n n' p1 r1 p2 r2. eapply starES. by econstructor.
  apply: (star_trans (m'.[n.:Var])). exact: red_subst.
  by apply: red_compat => -[|].
Qed.

Lemma pstep_subst sigma s t :
  pstep s t -> pstep s.[sigma] t.[sigma].
Proof.
  move=> A. elim: A sigma => /=; eauto using pstep.
  move=> A s1 s2 t1 t2 p1 ih1 p2 ih2 sigma. 
  replace (s2.[t2/].[sigma]) 
    with (s2.[up sigma].[t2.[sigma]/]) by autosubst.
  apply pstep_beta; eauto.
Qed.

Lemma pstep_ren s s' xi :
  pstep s s' -> pstep s.[ren xi] s'.[ren xi].
Proof.
  apply pstep_subst.
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof.
  move=> A [|n] //=. asimpl. apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau s t :
  psstep sigma tau -> pstep s t -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psstep_up.
  move=> A B. elim: B sigma tau A; asimpl...
  move=> A s1 s2 t1 t2 _ ih1 _ ih2 sigma tau C.
  replace (s2.[t2/].[tau]) 
    with (s2.[up tau].[t2.[tau]/]) by autosubst.
  apply pstep_beta; asimpl...
Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep s1.[t1/] s2.[t2/].
Proof.
  move=> A B. by apply: pstep_compat A => -[|].
Qed.

Lemma rho_triangle : triangle pstep rho.
Proof with eauto using pstep.
  move=> s t. elim=> {s t} //=...
  - move=> _ s1 s2 t1 t2 _ A _ B. exact: pstep_compat_beta.
  - move=> s1 s2 t1 t2 A ih1 _ ih2. case: s1 A ih1 => //=...
    move=> s t A ih1. inv A. inv ih1...
Qed.

Theorem church_rosser :
  CR step.
Proof with eauto using star.
  apply: (cr_method (e2 := pstep) (rho := rho))...
  exact: step_pstep.
  exact: pstep_red.
  exact: rho_triangle.
Qed.
Hint Resolve church_rosser.

Lemma red_sort_inv s A :
  Sort s ~>* A -> A = Sort s.
Proof.
  induction 1; intros; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_arrow_inv A B x :
  Arrow A B ~>* x -> 
  exists A' B',
    A ~>* A' /\
    B ~>* B' /\
    x = Arrow A' B'.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - firstorder.
    rewrite H3 in H0.
    inv H0.
    + exists A'.
      exists x0.
      repeat constructor; eauto using star.
    + exists x.
      exists B'.
      repeat constructor; eauto using star.
Qed.

Ltac red_inv m H :=
  match m with
  | Sort   => apply red_sort_inv in H
  | Arrow => apply red_arrow_inv in H
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
  end;
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  | [ H : value (App _ _) |- _ ] => inv H
  end; eauto.

Lemma sort_inv n m : Sort n === Sort m -> n = m.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_sort_inv in H0.
  apply red_sort_inv in H1.
  subst; inv H1; eauto.
Qed.

Lemma arrow_inv A1 A2 B1 B2 :
  Arrow A1 B1 === Arrow A2 B2 -> A1 === A2 /\ B1 === B2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_arrow_inv in H0.
  apply red_arrow_inv in H1.
  firstorder; subst.
  inv H4; eauto using join_conv.
  inv H4; eauto using join_conv.
Qed.

Notation 𝐔 l := (Sort (Some l)).
Notation 𝐏 := (Sort None).

Inductive sub1 : term ->term -> Prop :=
| sub1_refl A : sub1 A A
| sub1_prop l : sub1 𝐏 (𝐔 l)
| sub1_sort l1 l2 : l1 <= l2 -> sub1 (𝐔 l1) (𝐔 l2)
| sub1_arrow A B1 B2 : sub1 B1 B2 -> sub1 (Arrow A B1) (Arrow A B2).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 50, no associativity).

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_prop l : 𝐏 <: 𝐔 l.
Proof. exact/sub1_sub/sub1_prop. Qed.

Lemma sub_sort l1 l2 : l1 <= l2 -> 𝐔 l1 <: 𝐔 l2.
Proof. move=> leq. exact/sub1_sub/sub1_sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D => {A B}
  [A C D |n C D conv sb
  |n m leq C D conv sb
  |A B1 B2 sb1 ih C D conv sb2]...
  - inv sb... exfalso; solve_conv.
  - inv sb...
    + exfalso; solve_conv.
    + apply: sub_sort. move: conv => /sort_inv [eqn]. subst.
      exact: leq_trans leq _.
    + exfalso; solve_conv.
  - inv sb2...
    + exfalso; solve_conv.
    + exfalso; solve_conv.
    + move: conv => /arrow_inv[conv1 conv2].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_arrow... eapply conv_arrow... exact: conv_arrow.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub1_subst sigma A B : sub1 A B -> sub1 A.[sigma] B.[sigma].
Proof. move=> s. elim: s sigma => /=; eauto using sub1. Qed.

Lemma sub_subst sigma A B : A <: B -> A.[sigma] <: B.[sigma].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Reserved Notation "[ Γ |- ]".
Reserved Notation "[ Γ |- s :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| p_axiom Γ :
  [ Γ |- 𝐏 :- 𝐔 0 ]
| t_axiom Γ l :
  [ Γ |- 𝐔 l :- 𝐔 l.+1 ]
| ty_prop Γ A B n :
  [ Γ |- A :- Sort n ] ->
  [ A +: Γ |- B :- 𝐏 ] ->
  [ Γ |- Arrow A B :- 𝐏 ]
| ty_arrow Γ A B l :
  [ Γ |- A :- 𝐔 l ] ->
  [ A +: Γ |- B :- 𝐔 l ] ->
  [ Γ |- Arrow A B :- 𝐔 l ]
| ty_var Γ x A :
  [ x :- A ∈ Γ ] ->
  [ Γ |- Var x :- A ]
| ty_lam Γ A B s n :
  [ Γ |- Arrow A B :- Sort n ] ->
  [ A +: Γ |- s :- B ] ->
  [ Γ |- Lam A s :- Arrow A B ]
| ty_app Γ A B s t :
  [ Γ |- s :- Arrow A B ] ->
  [ Γ |- t :- A ] ->
  [ Γ |- App s t :- B.[t/] ]
| ty_conv Γ A B s n :
  A <: B ->
  [ Γ |- B :- Sort n ] ->
  [ Γ |- s :- A ] ->
  [ Γ |- s :- B ]
where "[ Γ |- s :- A ]" := (has_type Γ s A).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| s_ok Γ A n :
  [ Γ |- A :- Sort n ] ->
  [ Γ |- ] ->
  [ A +: Γ |- ]
| n_ok Γ :
  [ Γ |- ] ->
  [ □ Γ |- ]
where "[ Γ |- ]" := (context_ok Γ).

Notation "[ Γ |- s ]" := (exists n, [ Γ |- s :- Sort n ]).

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_s Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m +: Γ) (m.[ren ξ] +: Γ')
| agree_ren_n Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (□ Γ) (□ Γ')
| agree_ren_wk Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) (Γ) (m :: Γ').

Lemma agree_ren_refl Γ :
  agree_ren id Γ Γ.
Proof.
  induction Γ.
  - constructor.
  - destruct a. 
    assert (agree_ren id (t +: Γ) (t +: Γ)
      = agree_ren (upren id) (t +: Γ) (t.[ren id] +: Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (□ Γ) (□ Γ)
      = agree_ren (upren id) (□ Γ) (□ Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
Qed.

Lemma agree_ren_has Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  forall x A,
    [ x :- A ∈ Γ ] ->
    [ ξ x :- A.[ren ξ] ∈ Γ' ].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren ξ)]) 
      with (m0.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H; subst.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    destruct m; constructor; apply IHagree_ren; eauto.
Qed.

Lemma rename_ok Γ m A :
  [ Γ |- m :- A ] ->
  forall Γ' ξ,
    agree_ren ξ Γ Γ' ->
    [ Γ' |- m.[ren ξ] :- A.[ren ξ] ].
Proof.
  intros H.
  induction H; simpl; intros.
  - apply p_axiom; assumption.
  - apply t_axiom; assumption.
  - asimpl.
    eapply ty_prop; eauto.
    replace 𝐏 with (𝐏.[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    apply ty_arrow; eauto.
    replace (𝐔 l) with ((𝐔 l).[ren (upren ξ)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - replace (ids (ξ x)) with (Var (ξ x)) by autosubst.
    apply ty_var.
    eapply agree_ren_has; eauto.
  - eapply ty_lam.
    apply IHhas_type1; eauto.
    asimpl.
    apply IHhas_type2; eauto.
    constructor; eauto.
  - asimpl.
    specialize (IHhas_type1 _ _ H1).
    specialize (IHhas_type2 _ _ H1).
    asimpl in IHhas_type1.
    replace (B.[t.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[t.[ren ξ]/]) by autosubst.
    eapply ty_app; eauto.
  - eapply ty_conv.
    apply sub_subst; eauto.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
Qed.

Theorem weakening Γ s A B :
  [ Γ |- s :- A ] -> 
  [ B :: Γ |- s.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wk.
  apply agree_ren_refl.
Qed.

Axiom strong_normalization : forall Γ m A,
  [ Γ |- m :- A ] -> sn step m.