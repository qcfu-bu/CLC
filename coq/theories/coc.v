From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Logic.Classical_Prop.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CoC.

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
| Sort (n : nat)
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

Inductive pstep_cbv : term -> term -> Prop :=
| pstep_cbv_var x :
  pstep_cbv (Var x) (Var x)
| pstep_cbv_sort n :
  pstep_cbv (Sort n) (Sort n)
| pstep_cbv_lam s1 s2 :
  pstep_cbv s1 s2 ->
  pstep_cbv (Lam s1) (Lam s2)
| pstep_cbv_beta s1 s2 t1 t2 :
  pstep_cbv s1 s2 ->
  value t1 ->
  pstep_cbv t1 t2 ->
  pstep_cbv (App (Lam s1) t1) s2.[t2/]
| pstep_cbv_app s1 s2 t1 t2 :
  pstep_cbv s1 s2 ->
  pstep_cbv t1 t2 ->
  pstep_cbv (App s1 t1) (App s2 t2)
| pstep_cbv_prod s1 s2 t1 t2 :
  pstep_cbv s1 s2 ->
  pstep_cbv t1 t2 ->
  pstep_cbv (Prod s1 t1) (Prod s2 t2).

Notation red := (star pstep).
Notation red_cbv := (star pstep_cbv).
Notation "s === t" := (conv pstep s t) (at level 50).

Lemma pstep_refl s : pstep s s.
Proof.
  induction s; constructor; eauto.
Qed.

Lemma pstep_cbv_refl s : pstep_cbv s s.
Proof.
  induction s; constructor; eauto.
Qed.

Lemma pstep_value v v' : 
  pstep v v' -> value v ->  value v'.
Proof.
  induction 1; eauto; try constructor; intros; inv H1.
Qed.

Lemma pstep_cbv_value v v' : 
  pstep_cbv v v' -> value v ->  value v'.
Proof.
  induction 1; eauto; try constructor; intros.
  inv H2.
  inv H1.
Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep s1.[t1/] s2.[t2/].
Proof.
Admitted.

Lemma pstep_cbv_compat_beta s1 s2 t1 t2 :
  pstep_cbv s1 s2 -> pstep_cbv t1 t2 -> pstep_cbv s1.[t1/] s2.[t2/].
Proof.
Admitted.

Lemma pstep_cbv_ok s s' : pstep_cbv s s' -> pstep s s'.
Proof.
  induction 1; constructor; eauto.
Qed.

Axiom pstep_ren : forall s s' xi, 
  pstep s s' -> pstep s.[ren xi] s'.[ren xi].

Axiom pstep_cbv_ren : forall s s' xi, 
  pstep_cbv s s' -> pstep_cbv s.[ren xi] s'.[ren xi].

Axiom church_rosser : CR pstep.

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

Lemma pstep_cbv_ren_inv m n xi :
  pstep_cbv m.[ren xi] n ->
  left_invertible xi ->
    exists x, pstep_cbv m x /\ x.[ren xi] = n.
Proof.
  intro H.
  dependent induction H; intros.
  - inv H.
    exists ((Var x0).[ren x1]).
    rewrite x; asimpl.
    replace (xi >>> x1) with (x1 ∘ xi) by autosubst.
    rewrite H0; asimpl; firstorder.
    apply pstep_cbv_refl.
  - exists m; firstorder.
    apply pstep_cbv_refl.
  - destruct m; asimpl; try discriminate.
    inversion H0.
    inv x.
    assert (s.[up (ren xi)] = s.[ren (upren xi)]) by autosubst.
    apply left_invertible_upren in H0.
    pose proof (IHpstep_cbv s (upren xi) H2 H0).
    inv H3. inv H4.
    exists (Lam x); asimpl; firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    destruct m1; asimpl; try discriminate. inv H4.
    assert (s.[up (ren xi)] = s.[ren (upren xi)]) by autosubst.
    pose proof (left_invertible_upren H2).
    pose proof (IHpstep_cbv1 s (upren xi) H3 H4).
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    pose proof (IHpstep_cbv2 m2 xi H6 H2).
    firstorder; subst; asimpl.
    exists (x1.[x .: ids]); asimpl.
    firstorder.
    constructor; eauto.
    apply <- value_rename; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m1.[ren xi] = m1.[ren xi]) by eauto.
    assert (m2.[ren xi] = m2.[ren xi]) by eauto.
    apply IHpstep_cbv1 in H2; eauto.
    apply IHpstep_cbv2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (App x1 x).
    firstorder.
    constructor; eauto.
  - destruct m; asimpl; try discriminate. inv x.
    assert (m.[ren xi] = m.[ren xi]) by eauto.
    assert (t.[up (ren xi)] = t.[ren (upren xi)]) by autosubst.
    assert (left_invertible (upren xi)).
    apply left_invertible_upren; eauto.
    apply IHpstep_cbv1 in H2; eauto.
    apply IHpstep_cbv2 in H3; eauto.
    firstorder; subst; asimpl.
    exists (Prod x0 x1); asimpl; firstorder.
    constructor; eauto.
Qed.

Lemma pstep_cbv_ren1_inv m n :
  pstep_cbv m.[ren (+1)] n ->
    exists x, pstep_cbv m x /\ x.[ren (+1)] = n.
Proof.
  intros.
  apply pstep_cbv_ren_inv; eauto.
  unfold left_invertible.
  exists (predn).
  autosubst.
Qed.

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".
Reserved Notation "`[ Gamma |- s :- A ]".

Inductive raw_type : context term -> term -> term -> Prop :=
| raw_var Gamma x A :
  has Gamma x A ->
  `[ Gamma |- Var x :- A ]
| raw_sort Gamma n  :
  `[ Gamma |- Sort n :- Sort n.+1 ]
| raw_prod Gamma A B n :
  `[ Gamma |- A :- Sort n ] ->
  `[ A :s Gamma |- B :- Sort n ] ->
  `[ Gamma |- Prod A B :- Sort n ]
| raw_lam Gamma A B s n :
  `[ Gamma |- Prod A B :- Sort n ] ->
  `[ A :s Gamma |- s :- B ] ->
  `[ Gamma |- Lam s :- Prod A B ]
| raw_app Gamma A B s t :
  `[ Gamma |- s :- Prod A B ] ->
  `[ Gamma |- t :- A ] ->
  `[ Gamma |- App s t :- B.[t/] ]
| raw_conv Gamma A B s :
  A === B ->
  `[ Gamma |- s :- A ] ->
  `[ Gamma |- s :- B ]
where "`[ Gamma |- s :- A ]" := (raw_type Gamma s A).

Inductive has_type : context term -> term -> term -> Prop :=
| ty_var Gamma x A :
  has Gamma x A ->
  [ Gamma |- Var x :- A ]
| ty_sort Gamma n  :
  [ Gamma |- Sort n :- Sort n.+1 ]
| ty_prod Gamma A B n :
  [ Gamma |- A :- Sort n ] ->
  [ A :s Gamma |- B :- Sort n ] ->
  [ Gamma |- Prod A B :- Sort n ]
| ty_lam Gamma A B s n :
  [ Gamma |- Prod A B :- Sort n ] ->
  [ A :s Gamma |- s :- B ] ->
  [ Gamma |- Lam s :- Prod A B ]
| ty_app Gamma A B s t :
  [ Gamma |- s :- Prod A B ] ->
  [ Gamma |- t :- A ] ->
  [ Gamma |- App s t :- B.[t/] ]
| ty_conv Gamma A B s n :
  A === B ->
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

Theorem weakening Gamma s A B :
  [ Gamma |- s :- A ] -> 
  [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].
Proof.
Admitted.

Theorem preservation Gamma s A :
  [ Gamma |- ] -> 
  [ Gamma |- s :- A ] ->
  forall t, pstep s t -> [ Gamma |- t :- A ].
Proof.
Admitted.

Theorem progress s A :
  [ nil |- s :- A ] -> value s \/ exists s', step s s'.
Proof.
Admitted.

Axiom strong_cbv_norm : forall Gamma s A,
  [ Gamma |- ] ->
  [ Gamma |- s :- A ] ->
  exists v, value v /\ red_cbv s v.

Lemma raw_cbv_norm : forall Gamma s A,
  [ Gamma |- ] ->
  `[ Gamma |- s :- A ] ->
  exists v, value v /\ red_cbv s v.
Proof.
  intros.
  induction s.
  - eapply strong_cbv_norm; eauto.
    inv H0; constructor; eauto.

End CoC.