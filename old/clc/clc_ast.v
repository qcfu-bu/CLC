From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS clc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * AST of the Calculus of Linear Constructions

  Variable bindings use De Bruijn provided by the Autosubst library
  for capture avoiding substitutions. *)

Inductive term : Type :=
| Var   (x : var)
| Sort  (s : sort) (l : nat)
| Arrow (A : term) (B : {bind term}) (s : sort)
| Lolli (A : term) (B : {bind term}) (s : sort)
| Lam   (A : term) (n : {bind term}) (s : sort)
| App   (m n : term).

(** Derive basic sigma calculus lemmas using Autosubst. *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

(** Definition of values used by the progress theorem. *)

Inductive value : term -> Prop :=
| value_sort srt l  : value (Sort srt l)
| value_var x       : value (Var x)
| value_arrow A B s : value (Arrow A B s)
| value_lolli A B s : value (Lolli A B s)
| value_lam A n s   : value (Lam A n s).

(** Single-step reduction relation. *)

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta A m n s :
  (App (Lam A m s) n) ~> m.[n/]
| step_lamL A A' m s :
  A ~> A' ->
  Lam A m s ~> Lam A' m s
| step_lamR A m m' s :
  m ~> m' ->
  Lam A m s ~> Lam A m' s
| step_arrowL A A' B s :
  A ~> A' ->
  Arrow A B s ~> Arrow A' B s
| step_arrowR A B B' s :
  B ~> B' ->
  Arrow A B s ~> Arrow A B' s
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

(** Multi-step reduction is defined as the transitive reflexive
    closure of single-step reduction. 
      
    Two terms are definitionally equal if they are joinable by 
    multi-step reduction. *)

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).