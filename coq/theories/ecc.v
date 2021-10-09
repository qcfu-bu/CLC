From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Logic.Classical_Prop.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ECC.

Declare Scope coc_scope.
Open Scope coc_scope.

Definition context T := seq (option T).
Definition cons_Some T (n : T) (Gamma : context T) : context T := 
  Some n :: Gamma.
Definition cons_None T (Gamma : context T) : context T := 
  None :: Gamma.

Notation "m :s Gamma" := (cons_Some m Gamma) (at level 30).
Notation ":n Gamma" := (cons_None Gamma) (at level 30).

Inductive has {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| has_O m Gamma :
  has (m :s Gamma) 0 m.[ren (+1)]
| has_S Gamma v m n : 
  has Gamma v m ->
  has (n :s Gamma) (v.+1) m.[ren (+1)]
| has_N Gamma v m : 
  has Gamma v m ->
  has (:n Gamma) (v.+1) m.[ren (+1)].

Lemma has_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  has Gamma x A ->
  forall B,
    has Gamma x B ->
    A = B.
Proof.
  induction 1; intros.
  inv H1; eauto.
  inv H2; eauto.
  apply IHhas in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhas in H5. rewrite H5; eauto.
Qed.
  
Inductive term : Type :=
| Var (x : var)
| Sort (n : option nat)
| App  (s t : term)
| Lam  (s : {bind term})
| Prod (s : term) (t : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort l   : value (Sort l)
| value_var x    : value (Var x)
| value_prod A B : value (Prod A B)
| value_lam n    : value (Lam n).

Inductive step : term -> term -> Prop :=
| step_beta s t :
  step (App (Lam s) t) s.[t/]
| step_appL s1 s2 t :
  step s1 s2 ->
  step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
  step t1 t2 ->
  step (App s t1) (App s t2).

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort n :
  pstep (Sort n) (Sort n)
| pstep_lam s1 s2 :
  pstep s1 s2 ->
  pstep (Lam s1) (Lam s2)
| pstep_beta s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (App (Lam s1) t1) s2.[t2/]
| pstep_app s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (App s1 t1) (App s2 t2)
| pstep_prod s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (Prod s1 t1) (Prod s2 t2).

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

Definition psstep (sigma tau : var -> term) :=
  forall x, pstep (sigma x) (tau x).

Fixpoint rho (s : term) : term :=
  match s with
    | App (Lam s) t => (rho s).[rho t/]
    | App s t => App (rho s) (rho t)
    | Lam s => Lam (rho s)
    | Prod A B => Prod (rho A) (rho B)
    | x => x
  end.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof. elim; eauto using pstep. Qed.

Lemma pstep_subst sigma s t :
  pstep s t -> pstep s.[sigma] t.[sigma].
Proof.
  move=> A. elim: A sigma => /=; eauto using pstep.
  move=> s1 s2 t1 t2 p1 ih1 p2 ih2 sigma. 
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
  move=> s1 s2 t1 t2 _ A _ B sigma tau C.
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
  - move=> s1 s2 t1 t2 _ A _ B. exact: pstep_compat_beta.
  - move=> s1 s2 t1 t2 A ih1 _ ih2. case: s1 A ih1 => //=...
    move=> s A ih1. inv A. inv ih1...
Qed.

Theorem church_rosser :
  CR pstep.
Proof with eauto using star.
  apply: (cr_method (e2 := pstep) (rho := rho))...
  exact: rho_triangle.
Qed.
Hint Resolve church_rosser.

Definition sconv (sigma tau : var -> term) :=
  forall x, sigma x === tau x.

Lemma conv_app s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> App s1 t1 === App s2 t2.
Proof.
  move=> A B. apply: (conv_trans (App s2 t1)).
  - apply: (conv_hom (App^~ t1)) A => x y p. by apply: pstep_app.
  - apply: conv_hom B => x y p. by apply: pstep_app.
Qed.

Lemma conv_lam s1 s2 : s1 === s2 -> Lam s1 === Lam s2.
Proof. apply: conv_hom => x y. exact: pstep_lam. Qed.

Lemma conv_prod s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> Prod s1 t1 === Prod s2 t2.
Proof.
  move=> A B. apply: (conv_trans (Prod s2 t1)).
  - apply: (conv_hom (Prod^~ t1)) A => x y p. by apply: pstep_prod.
  - apply: conv_hom B => x y p. by apply: pstep_prod.
Qed.

Lemma conv_subst sigma s t : s === t -> s.[sigma] === t.[sigma].
Proof. apply: conv_hom. intros. apply: pstep_subst. eauto. Qed.

Definition left_invertible (f : nat -> nat) := 
  exists g, g ∘ f = id.

Lemma left_invertible_upren xi :
  left_invertible xi -> left_invertible (upren xi).
Proof.
  unfold left_invertible.
  intros.
  inv H.
  exists (upren x).
  assert (upren x ∘ upren xi = upren xi >>> upren x) by autosubst.
  rewrite H; asimpl.
  replace (xi >>> x) with (x ∘ xi) by autosubst.
  rewrite H0; autosubst.
Qed.

Lemma sort_ren_inv l v xi :
  Sort l = v.[ren xi] -> v = Sort l.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma var_ren_inv x v xi :
  Var x = v.[ren xi] -> exists n, v = Var n.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma prod_ren_inv A B v xi :
  Prod A B = v.[ren xi] -> exists A' B', v = Prod A' B'.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma lam_ren_inv m v xi :
  Lam m = v.[ren xi] -> exists n, v = Lam n.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma value_rename v xi :
  value v <-> value v.[ren xi].
Proof.
  split.
  induction 1; asimpl; constructor.
  intros.
  dependent induction H.
  apply sort_ren_inv in x; subst.
  constructor.
  apply var_ren_inv in x.
  inv x.
  constructor.
  apply prod_ren_inv in x.
  inv x. inv H.
  constructor.
  apply lam_ren_inv in x.
  inv x.
  constructor.
Qed.

Lemma red_sort_inv s A :
  red (Sort s) A -> A = (Sort s).
Proof.
  induction 1; intros; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_prod_inv A B x :
  red (Prod A B) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Prod A' B'.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - firstorder.
    rewrite H3 in H0.
    inv H0.
    exists s2.
    exists t2.
    repeat constructor; eauto using star.
Qed.

Ltac red_inv m H :=
  match m with
  | Sort   => apply red_sort_inv in H
  | Prod => apply red_prod_inv in H
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

Lemma prod_inv A1 A2 B1 B2 :
  Prod A1 B1 === Prod A2 B2 -> A1 === A2 /\ B1 === B2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_prod_inv in H0.
  apply red_prod_inv in H1.
  firstorder; subst.
  inv H4; eauto using join_conv.
  inv H4; eauto using join_conv.
Qed.

Notation "@ l" := (Sort (Some l)) (at level 30).
Notation prop := (Sort None).

Inductive sub1 : term ->term -> Prop :=
| sub1_refl A : sub1 A A
| sub1_prop n : sub1 prop (@n)
| sub1_sort n m : n <= m -> sub1 (@n) (@m)
| sub1_prod A B1 B2 : sub1 B1 B2 -> sub1 (Prod A B1) (Prod A B2).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 50, no associativity) : coc_scope.

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_prop n : prop <: @n.
Proof. exact/sub1_sub/sub1_prop. Qed.

Lemma sub_sort n m : n <= m -> @n <: @m.
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
    + move: conv => /prod_inv[conv1 conv2].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_prod... eapply conv_prod... exact: conv_prod.
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

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| p_axiom Gamma :
  [ Gamma |- prop :- @0 ]
| t_axiom Gamma n :
  [ Gamma |- @n :- @n.+1 ]
| ty_prop Gamma A B n :
  [ Gamma |- A :- Sort n ] ->
  [ A :s Gamma |- B :- prop ] ->
  [ Gamma |- Prod A B :- prop ]
| ty_prod Gamma A B n :
  [ Gamma |- A :- @n ] ->
  [ A :s Gamma |- B :- @n ] ->
  [ Gamma |- Prod A B :- @n ]
| ty_var Gamma x A :
  has Gamma x A ->
  [ Gamma |- Var x :- A ]
| ty_lam Gamma A B s n :
  [ Gamma |- Prod A B :- Sort n ] ->
  [ A :s Gamma |- s :- B ] ->
  [ Gamma |- Lam s :- Prod A B ]
| ty_app Gamma A B s t :
  [ Gamma |- s :- Prod A B ] ->
  [ Gamma |- t :- A ] ->
  [ Gamma |- App s t :- B.[t/] ]
| ty_conv Gamma A B s n :
  A <: B ->
  [ Gamma |- B :- Sort n ] ->
  [ Gamma |- s :- A ] ->
  [ Gamma |- s :- B ]
where "[ Gamma |- s :- A ]" := (has_type Gamma s A).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| s_ok Gamma A n :
  [ Gamma |- A :- Sort n ] ->
  [ Gamma |- ] ->
  [ A :s Gamma |- ]
| n_ok Gamma :
  [ Gamma |- ] ->
  [ :n Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Notation "[ Gamma |- s ]" := (exists n, [ Gamma |- s :- Sort n ]).

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil xi :
  agree_ren xi nil nil
| agree_ren_s Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m :s Gamma) (m.[ren xi] :s Gamma')
| agree_ren_n Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (:n Gamma) (:n Gamma')
| agree_ren_wk Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) (Gamma) (m :: Gamma').

Lemma agree_ren_refl Gamma :
  agree_ren id Gamma Gamma.
Proof.
  induction Gamma.
  - constructor.
  - destruct a. 
    assert (agree_ren id (t :s Gamma) (t :s Gamma)
      = agree_ren (upren id) (t :s Gamma) (t.[ren id] :s Gamma))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (:n Gamma) (:n Gamma)
      = agree_ren (upren id) (:n Gamma) (:n Gamma))
      by autosubst.
    rewrite H.
    constructor; eauto.
Qed.

Lemma agree_ren_has Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  forall x A,
    has Gamma x A ->
    has Gamma' (xi x) A.[ren xi].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H; subst.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    destruct m; constructor; apply IHagree_ren; eauto.
Qed.

Lemma rename_ok Gamma m A :
  [ Gamma |- m :- A ] ->
  forall Gamma' xi,
    agree_ren xi Gamma Gamma' ->
    [ Gamma' |- m.[ren xi] :- A.[ren xi] ].
Proof.
  intros H.
  induction H; simpl; intros.
  - apply p_axiom; assumption.
  - apply t_axiom; assumption.
  - asimpl.
    eapply ty_prop; eauto.
    replace prop with (prop.[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    apply ty_prod; eauto.
    replace (@n) with ((@n).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
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
    replace (B.[t.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[t.[ren xi]/]) by autosubst.
    eapply ty_app; eauto.
  - eapply ty_conv.
    apply sub_subst; eauto.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
Qed.

Theorem weakening Gamma s A B :
  [ Gamma |- s :- A ] -> 
  [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wk.
  apply agree_ren_refl.
Qed.

Close Scope coc_scope.

End ECC.
