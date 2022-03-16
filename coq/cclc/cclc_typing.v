From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_subtype clc_typing
  cclc_ast cclc_dual.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ p" (at level 50, p at next level).

Inductive cclc_type : context term -> proc -> Prop :=
| cclc_exp Γ m A s :
  Γ ⊢ m : A : s ->
  Γ ⊢ ⟨ m ⟩
| cclc_par Γ1 Γ2 Γ p q :
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ p ->
  Γ2 ⊢ q ->
  Γ ⊢ p ∣ q
| cclc_scope Γ p A B i :
  A ~ B ->
  [Γ] ⊢ Ch A : L @ i : U ->
  [Γ] ⊢ Ch B : L @ i : U ->
  Ch A.[ren (+1)] :L Ch B :L Γ ⊢ p ->
  Γ ⊢ ν.p
where "Γ ⊢ p" := (cclc_type Γ p).