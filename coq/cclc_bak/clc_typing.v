From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).

Inductive clc_type : context term -> term -> term -> Prop :=
| clc_axiom Γ s l :
  Γ |> U ->
  Γ ⊢ s @ l : U @ l.+1
| clc_pi Γ A B s r t i :
  Γ |> U ->
  Γ ⊢ A : s @ i ->
  [A :{s} Γ] ⊢ B : r @ i ->
  Γ ⊢ Pi A B s t : t @ i
| clc_var Γ x A s :
  has Γ x s A ->
  Γ ⊢ Var x : A
| clc_lam Γ A B m s t i :
  Γ |> t ->
  [Γ] ⊢ Pi A B s t : t @ i ->
  A :{s} Γ ⊢ m : B ->
  Γ ⊢ Lam A m s t : Pi A B s t
| clc_app Γ1 Γ2 Γ A B m n s t :
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Pi A B s t ->
  Γ2 ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| clc_unit Γ :
  Γ |> U ->
  Γ ⊢ Unit : U @ 0
| clc_it Γ :
  Γ |> U ->
  Γ ⊢ It : Unit
| clc_sigma Γ A B s r t i :
  s ⋅ r ≤ t ->
  Γ |> U ->
  Γ ⊢ A : s @ i ->
  [A :{s} Γ] ⊢ B : r @ i ->
  Γ ⊢ Sigma A B s r t : t @ i
| clc_pair Γ1 Γ2 Γ A B m n s r t i :
  Γ1 |> s ->
  Γ2 |> r ->
  Γ1 ∘ Γ2 => Γ ->
  [Γ] ⊢ Sigma A B s r t : t @ i ->
  Γ1 ⊢ m : A ->
  Γ2 ⊢ n : B.[m/] ->
  Γ ⊢ Pair m n t : Sigma A B s r t
| clc_letin1 Γ1 Γ2 Γ m n A :
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Unit ->
  Γ2 ⊢ n : A ->
  Γ ⊢ LetIn1 m n : A
| clc_letin2 Γ1 Γ2 Γ A B C m n s r t k x i :
  t ≤ k ->
  Γ1 |> k ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Sigma A B s r t ->
  [Sigma A B s r t :{k} Γ2] ⊢ C : x @ i ->
  B :{r} A :{s} Γ2 ⊢ n : C.[Pair (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn2 m n : C.[m/]
| clc_conv Γ A B m s i :
  A <: B ->
  Γ ⊢ m : A ->
  [Γ] ⊢ B : s @ i ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (clc_type Γ m A).

Inductive ok : context term -> Prop :=
| nil_ok :
  ok nil
| ty_ok Γ A s l :
  ok Γ ->
  [Γ] ⊢ A : s @ l ->
  ok (A :{s} Γ)
| n_ok Γ :
  ok Γ ->
  ok (_: Γ).

Lemma re_ok Γ : ok Γ -> ok [Γ].
Proof with eauto using ok.
  elim=>{Γ}...
  move=>Γ A [|] l wf1 wf2 ty//=.
  apply: ty_ok... rewrite<-re_invo; eauto.
  apply: n_ok...
Qed.