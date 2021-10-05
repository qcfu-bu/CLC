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

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

Lemma pstep_refl s : pstep s s.
Proof.
  induction s; constructor; eauto.
Qed.

Lemma pstep_value v v' : 
  pstep v v' -> value v ->  value v'.
Proof.
  induction 1; eauto; try constructor; intros; inv H1.
Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep s1.[t1/] s2.[t2/].
Proof.
Admitted.

Axiom pstep_ren : forall s s' xi, 
  pstep s s' -> pstep s.[ren xi] s'.[ren xi].

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

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".

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

End CoC.