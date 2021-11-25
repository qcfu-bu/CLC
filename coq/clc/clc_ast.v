From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS clc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var   (x : var)
| Sort  (s : sort) (l : option nat)
| Prod  (A : term) (B : {bind term}) (s : sort)
| Lolli (A : term) (B : {bind term}) (s : sort)
| Lam   (n : {bind term})
| App   (m n : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort srt l  : value (Sort srt l)
| value_var x       : value (Var x)
| value_prod A B s  : value (Prod A B s)
| value_lolli A B s : value (Lolli A B s)
| value_lam n       : value (Lam n).

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta m n :
  (App (Lam m) n) ~> m.[n/]
| step_lam m m' :
  m ~> m' ->
  Lam m ~> Lam m'
| step_prodL A A' B s :
  A ~> A' ->
  Prod A B s ~> Prod A' B s
| step_prodR A B B' s :
  B ~> B' ->
  Prod A B s ~> Prod A B' s
| step_lolliL A A' B s :
  A ~> A' ->
  Lolli A B s ~> Lolli A' B s
| step_lolliR A B B' s :
  B ~> B' ->
  Lolli A B s ~> Lolli A B' s
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