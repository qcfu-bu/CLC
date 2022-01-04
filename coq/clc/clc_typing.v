From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Typing Rules of CLC *)

Reserved Notation "[ Γ |- ]".
Reserved Notation "[ Γ |- m :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| s_axiom Γ s l : 
  pure Γ ->
  [ Γ |- s @ l :- U @ l.+1 ]
| u_arrow Γ A B s l :
  pure Γ ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- B :- s @ l ] ->
  [ Γ |- Arrow A B U :- U @ l ]
| l_arrow Γ A B s l :
  pure Γ ->
  [ Γ |- A :- L @ l ] ->
  [ +n Γ |- B :- s @ l ] ->
  [ Γ |- Arrow A B L :- U @ l ]
| u_lolli Γ A B s l :
  pure Γ ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- B :- s @ l ] ->
  [ Γ |- Lolli A B U :- L @ l ]
| l_lolli Γ A B s l :
  pure Γ ->
  [ Γ |- A :- L @ l ] ->
  [ +n Γ |- B :- s @ l ] ->
  [ Γ |- Lolli A B L :- L @ l ]
| u_var Γ x A : 
  hasU Γ x A ->
  [ Γ |- Var x :- A ]
| l_var Γ x A :
  hasL Γ x A ->
  [ Γ |- Var x :- A ]
| arrow_lam Γ n A B s t l :
  pure Γ ->
  [ Γ |- Arrow A B s :- t @ l ] ->
  [ A +{s} Γ |- n :- B ] ->
  [ Γ |- Lam A n s :- Arrow A B s ]
| lolli_lam Γ n A B s t l :
  [ re Γ |- Lolli A B s :- t @ l ] ->
  [ A +{s} Γ |- n :- B ] ->
  [ Γ |- Lam A n s :- Lolli A B s ]
| u_arrow_app Γ1 Γ2 Γ A B m n :
  pure Γ2 ->
  [ Γ1 |- m :- Arrow A B U ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| l_arrow_app Γ1 Γ2 Γ  A B m n :
  [ Γ1 |- m :- Arrow A B L ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| u_lolli_app Γ1 Γ2 Γ A B m n :
  pure Γ2 ->
  [ Γ1 |- m :- Lolli A B U ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| l_lolli_app Γ1 Γ2 Γ  A B m n :
  [ Γ1 |- m :- Lolli A B L ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| conversion Γ A B m s l :
  A <: B ->
  [ re Γ |- B :- Sort s l ] ->
  [ Γ |- m :- A ] ->
  [ Γ |- m :- B ]
where "[ Γ |- m :- A ]" := (has_type Γ m A).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| u_ok Γ A l :
  [ Γ |- ] ->
  [ re Γ |- A :- Sort U l ] ->
  [ A +u Γ |- ]
| l_ok Γ A l :
  [ Γ |- ] ->
  [ re Γ |- A :- Sort L l ] ->
  [ A +l Γ |- ]
| n_ok Γ :
  [ Γ |- ] ->
  [ +n Γ |- ]
where "[ Γ |- ]" := (context_ok Γ).

Lemma re_ok Γ :
  [ Γ |- ] ->
  [ re Γ |- ].
Proof with eauto using context_ok.
  intros.
  induction H...
  simpl.
  eapply u_ok...
  rewrite <- re_re; eauto.
Qed.