From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var (x : var)
| TySort
| LnSort
| TyProd (s : term) (t : {bind term})
| LnProd (s : term) (t : {bind term})
| Lambda (s : {bind term})
| App (s t : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive step : term -> term -> Prop :=
| step_beta s t u :
  u = s.[t/] -> step (App (Lambda s) t) u
| step_appL s1 s2 t :
  step s1 s2 -> step (App s1 t) (App s2 t)
| step_lam s1 s2 :
  step s1 s2 -> step (Lambda s1) (Lambda s2)
| step_tyProdL A1 A2 B :
  step A1 A2 -> step (TyProd A1 B) (TyProd A2 B)
| step_lnProdL A1 A2 B :
  step A1 A2 -> step (LnProd A1 B) (LnProd A2 B)
| step_tyProdR A B1 B2 :
  step B1 B2 -> step (TyProd A B1) (TyProd A B2)
| step_lnProdR A B1 B2 :
  step B1 B2 -> step (LnProd A B1) (LnProd A B2).