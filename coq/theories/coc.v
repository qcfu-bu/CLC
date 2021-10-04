From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program.
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
| step_beta s t : step (App (Lam s) t) s.[t/]
| step_appL s1 s2 t :
  step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
  step t1 t2 -> step (App s t1) (App s t2)
| step_lam s1 s2 :
  step s1 s2 -> step (Lam s1) (Lam s2)
| step_prodL A1 A2 B :
  step A1 A2 -> step (Prod A1 B) (Prod A2 B)
| step_prodR A B1 B2 :
  step B1 B2 -> step (Prod A B1) (Prod A B2).

Inductive pstep : term -> term -> Prop :=
| pstep_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep (App (Lam s1) t1) s2.[t2/]
| pstep_var x : pstep (Var x) (Var x)
| pstep_sort n : pstep (Sort n) (Sort n)
| pstep_app s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep (App s1 t1) (App s2 t2)
| pstep_lam s1 s2 :
  pstep s1 s2 -> pstep (Lam s1) (Lam s2)
| pstep_prod s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep (Prod s1 t1) (Prod s2 t2).

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

Lemma pstep_refl s : pstep s s.
Proof.
  induction s; constructor; eauto.
Qed.

Axiom pstep_ren : forall s s' xi, 
  pstep s s' -> pstep s.[ren xi] s'.[ren xi].
Axiom church_rosser : CR pstep.

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
| ty_conv Gamma A B s :
  A === B ->
  [ Gamma |- s :- A ] ->
  [ Gamma |- s :- B ]
where "[ Gamma |- s :- A ]" := (has_type Gamma s A).

Inductive context_ok : context term -> Prop :=
| ctx_nil :
  [ nil |- ]
| ctx_ncons Gamma A n :
  [ Gamma |- A :- Sort n ] ->
  [ Gamma |- ] ->
  [ A :s Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Notation "[ Gamma |- s ]" := (exists n, [ Gamma |- s :- Sort n ]).

Axiom weakening : 
  forall Gamma s A B,
  [ Gamma |- s :- A ] -> [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].

Axiom preservation :
  forall Gamma s A,
  [ Gamma |- ] -> 
  [ Gamma |- s :- A ] ->
  forall t, pstep s t -> [ Gamma |- t :- A ].

Axiom progress :
  forall s A,
  [ nil |- s :- A ] -> value s \/ exists s', step s s'.

Axiom strong_norm :
  forall Gamma s A,
  [ Gamma |- ] ->
  [ Gamma |- s :- A ] ->
  exists v, value v /\ s === v.

End CoC.