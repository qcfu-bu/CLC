From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sort := U | L.

Inductive term : Type :=
(* core *)
| Var    (x : var)
| Sort   (s : sort)
| Pi     (A : term) (B : {bind term}) (s : sort)
| Lam    (A : term) (m : {bind term}) (s : sort)
| App    (m n : term)
| Fix    (A : term) (m : {bind term})
(* data *)
| Unit
| It
| Either
| Left
| Right
| Sigma  (A : term) (B : {bind term}) (s : sort)
| Pair   (m n : term) (t : sort)
| Case   (m n1 n2 : term)
| LetIn1 (m n : term)
| LetIn2 (m : term) (n : {bind 2 of term})
(* session *)
| Main
| Proto
| Stop   (r : bool)
| Act    (r : bool) (A : term) (B : {bind term})
| Ch     (r : bool) (A : term)
| Fork   (m n : term)
| Recv   (ch : term)
| Send   (ch : term)
| Close  (ch : term)
| Wait   (ch : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
