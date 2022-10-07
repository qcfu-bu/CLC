From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Export cclc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ p" (at level 50, p at next level).

Inductive cclc_type : context term -> proc -> Prop :=
| cclc_exp Γ m A :
  Γ ⊢ m : A ->
  Γ ⊢ ⟨ m ⟩
| cclc_par Γ1 Γ2 Γ p q :
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ p ->
  Γ2 ⊢ q ->
  Γ ⊢ p ∣ q
| cclc_scope Γ p r1 r2 A :
  r1 = ~~r2 ->
  [Γ] ⊢ A : Proto ->
  Ch r1 A.[ren (+1)] :L Ch r2 A :L Γ ⊢ p ->
  Γ ⊢ ν.p
where "Γ ⊢ p" := (cclc_type Γ p).
