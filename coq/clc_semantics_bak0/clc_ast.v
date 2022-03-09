From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var    (x : var)
| Sort   (s : sort) (l : nat)
| Pi     (A : term) (B : {bind term}) (s r t : sort)
| Lam    (m : {bind term}) (s t : sort)
| App    (m n : term)
| Unit
| It
| Sigma  (A : term) (B : {bind term}) (s r t : sort)
| Pair   (m n : term) (t : sort)
| LetIn1 (m n : term)
| LetIn2 (m : term) (n : {bind 2 of term})
| Ptr    (l : nat).

Notation "s @ l" := (Sort s l) (at level 30).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta m n s t :
  (App (Lam m s t) n) ~> m.[n/]
| step_lam m m' s t :
  m ~> m' ->
  Lam m s t ~> Lam m' s t
| step_piL A A' B s r t :
  A ~> A' ->
  Pi A B s r t ~> Pi A' B s r t
| step_piR A B B' s r t :
  B ~> B' ->
  Pi A B s r t ~> Pi A B' s r t
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| step_sigmaL A A' B s r t :
  A ~> A' ->
  Sigma A B s r t ~> Sigma A' B s r t
| step_sigmaR A B B' s r t :
  B ~> B' ->
  Sigma A B s r t ~> Sigma A B' s r t
| step_pairL m m' n t :
  m ~> m' ->
  Pair m n t ~> Pair m' n t
| step_pairR m n n' t :
  n ~> n' ->
  Pair m n t ~> Pair m n' t
| step_letin1L m m' n :
  m ~> m' ->
  LetIn1 m n ~> LetIn1 m' n
| step_letin1R m n n' :
  n ~> n' ->
  LetIn1 m n ~> LetIn1 m n'
| step_iota1 n :
  LetIn1 It n ~> n
| step_letin2L m m' n :
  m ~> m' ->
  LetIn2 m n ~> LetIn2 m' n
| step_letin2R m n n' :
  n ~> n' ->
  LetIn2 m n ~> LetIn2 m n'
| step_iota2 m1 m2 n t :
  LetIn2 (Pair m1 m2 t) n ~> n.[m2,m1/]
where "m ~> n" := (step m n).

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).