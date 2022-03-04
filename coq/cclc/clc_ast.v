From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical.
Require Import AutosubstSsr ARS clc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var (x : var)
| Sort (s : sort) (l : nat)
| Pi (A : term) (B : {bind term}) (s t : sort)
| Lam (A : term) (B : {bind term}) (s t : sort)
| App (m n : term).

Notation "s @ l" := (Sort s l) (at level 30).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta A m n s t :
  (App (Lam A m s t) n) ~> m.[n/]
| step_lamL A A' m s t :
  A ~> A' ->
  Lam A m s t ~> Lam A' m s t
| step_lamR A m m' s t :
  m ~> m' ->
  Lam A m s t ~> Lam A m' s t
| step_piL A A' B s t :
  A ~> A' ->
  Pi A B s t ~> Pi A' B s t
| step_piR A B B' s t :
  B ~> B' ->
  Pi A B s t ~> Pi A B' s t
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
where "m ~> n" := (step m n).

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).