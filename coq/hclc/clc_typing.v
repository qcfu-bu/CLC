From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ m : A : s" 
  (at level 50, m, A, s at next level).

Inductive clc_type : context term -> term -> term -> sort -> Prop :=
| clc_axiom Γ s l :
  Γ |> U ->
  Γ ⊢ s @ l : U @ l.+1 : U
| clc_pi Γ A B s r t i :
  Γ |> U ->
  Γ ⊢ A : s @ i : U ->
  [A :{s} Γ] ⊢ B : r @ i : U ->
  Γ ⊢ Pi A B s r t : t @ i : U
| clc_var Γ x A s :
  has Γ x s A ->
  Γ ⊢ Var x : A : s
| clc_lam Γ A B m s r t i :
  Γ |> t ->
  [Γ] ⊢ Pi A B s r t : t @ i : U ->
  A :{s} Γ ⊢ m : B : r ->
  Γ ⊢ Lam A m s t : Pi A B s r t : t
| clc_app Γ1 Γ2 Γ A B m n s r t :
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Pi A B s r t : t ->
  Γ2 ⊢ n : A : s ->
  Γ ⊢ App m n : B.[n/] : r
| clc_unit Γ :
  Γ |> U ->
  Γ ⊢ Unit : U @ 0 : U
| clc_it Γ :
  Γ |> U ->
  Γ ⊢ It : Unit : U
| clc_bool Γ :
  Γ |> U ->
  Γ ⊢ Bool : U @ 0 : U
| clc_left Γ :
  Γ |> U ->
  Γ ⊢ Left : Bool : U
| clc_right Γ :
  Γ |> U ->
  Γ ⊢ Right : Bool : U
| clc_sigma Γ A B s r t i :
  s ⋅ r ≤ t ->
  Γ |> U ->
  Γ ⊢ A : s @ i : U ->
  [A :{s} Γ] ⊢ B : r @ i : U ->
  Γ ⊢ Sigma A B s r t : t @ i : U
| clc_pair Γ1 Γ2 Γ A B m n s r t i :
  Γ1 |> s ->
  Γ2 |> r ->
  Γ1 ∘ Γ2 => Γ ->
  [Γ] ⊢ Sigma A B s r t : t @ i : U ->
  Γ1 ⊢ m : A : s ->
  Γ2 ⊢ n : B.[m/] : r ->
  Γ ⊢ Pair m n t : Sigma A B s r t : t
| clc_case Γ1 Γ2 Γ m n1 n2 A s t i :
  Γ1 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Bool : U ->
  [Bool :{s} Γ2] ⊢ A : t @ i : U ->
  Γ2 ⊢ n1 : A.[Left/] : t ->
  Γ2 ⊢ n2 : A.[Right/] : t ->
  Γ ⊢ Case m n1 n2 : A.[m/] : t
| clc_letin1 Γ1 Γ2 Γ m n A s :
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Unit : U ->
  Γ2 ⊢ n : A : s ->
  Γ ⊢ LetIn1 m n : A : s
| clc_letin2 Γ1 Γ2 Γ A B C m n s r t k x i :
  t ≤ k ->
  Γ1 |> k ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Sigma A B s r t : t ->
  [Sigma A B s r t :{k} Γ2] ⊢ C : x @ i : U ->
  B :{r} A :{s} Γ2 ⊢ n : C.[Pair (Var 1) (Var 0) t .: ren (+2)] : x ->
  Γ ⊢ LetIn2 m n : C.[m/] : x
| clc_conv Γ A B m s i :
  A <: B ->
  Γ ⊢ m : A : s ->
  [Γ] ⊢ B : s @ i : U ->
  Γ ⊢ m : B : s
where "Γ ⊢ m : A : s" := (clc_type Γ m A s).

Inductive ok : context term -> Prop :=
| nil_ok :
  ok nil
| ty_ok Γ A s l :
  ok Γ ->
  [Γ] ⊢ A : s @ l : U ->
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
