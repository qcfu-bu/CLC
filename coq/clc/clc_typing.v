From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Typing Rules of CLC *)

Notation 𝐏 := (Sort U None).
Reserved Notation "[ Γ |- ]".
Reserved Notation "[ Γ |- m :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| p_axiom Γ : 
  [ Γ ] ->
  [ Γ |- 𝐏 :- U @ 0 ]
| s_axiom Γ s l : 
  [ Γ ] ->
  [ Γ |- s @ l :- U @ l.+1 ]
| prop Γ A B l :
  [ Γ ] ->
  [ Γ |- A :- Sort U l ] ->
  [ A +u Γ |- B :- 𝐏 ] ->
  [ Γ |- Prod A B U :- 𝐏 ]
| u_prod Γ A B s l :
  [ Γ ] ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- B :- s @ l ] ->
  [ Γ |- Prod A B U :- U @ l ]
| l_prod Γ A B s l :
  [ Γ ] ->
  [ Γ |- A :- L @ l ] ->
  [ □ Γ |- B :- s @ l ] ->
  [ Γ |- Prod A B L :- U @ l ]
| u_lolli Γ A B s l :
  [ Γ ] ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- B :- s @ l ] ->
  [ Γ |- Lolli A B U :- L @ l ]
| l_lolli Γ A B s l :
  [ Γ ] ->
  [ Γ |- A :- L @ l ] ->
  [ □ Γ |- B :- s @ l ] ->
  [ Γ |- Lolli A B L :- L @ l ]
| u_var Γ x A : 
  [ x :u A ∈ Γ ] ->
  [ Γ |- Var x :- A ]
| l_var Γ x A :
  [ x :l A ∈ Γ ] ->
  [ Γ |- Var x :- A ]
| prod_lam Γ n A B s t l :
  [ Γ ] ->
  [ Γ |- Prod A B s :- Sort t l ] ->
  [ A +{s} Γ |- n :- B ] ->
  [ Γ |- Lam n :- Prod A B s ]
| lolli_lam Γ n A B s t l :
  [ %Γ |- Lolli A B s :- Sort t l ] ->
  [ A +{s} Γ |- n :- B ] ->
  [ Γ |- Lam n :- Lolli A B s ]
| u_prod_app Γ1 Γ2 Γ A B m n :
  [ Γ2 ] ->
  [ Γ1 |- m :- Prod A B U ] ->
  [ Γ2 |- n :- A ] ->
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ Γ |- App m n :- B.[n/] ]
| l_prod_app Γ1 Γ2 Γ  A B m n :
  [ Γ1 |- m :- Prod A B L ] ->
  [ Γ2 |- n :- A ] ->
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ Γ |- App m n :- B.[n/] ]
| u_lolli_app Γ1 Γ2 Γ A B m n :
  [ Γ2 ] ->
  [ Γ1 |- m :- Lolli A B U ] ->
  [ Γ2 |- n :- A ] ->
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ Γ |- App m n :- B.[n/] ]
| l_lolli_app Γ1 Γ2 Γ  A B m n :
  [ Γ1 |- m :- Lolli A B L ] ->
  [ Γ2 |- n :- A ] ->
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ Γ |- App m n :- B.[n/] ]
| conversion Γ A B m s l :
  A <: B ->
  [ %Γ |- B :- Sort s l ] ->
  [ Γ |- m :- A ] ->
  [ Γ |- m :- B ]
where "[ Γ |- m :- A ]" := (has_type Γ m A).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| u_ok Γ A l :
  [ Γ |- ] ->
  [ %Γ |- A :- Sort U l ] ->
  [ A +u Γ |- ]
| l_ok Γ A l :
  [ Γ |- ] ->
  [ %Γ |- A :- Sort L l ] ->
  [ A +l Γ |- ]
| n_ok Γ :
  [ Γ |- ] ->
  [ □ Γ |- ]
where "[ Γ |- ]" := (context_ok Γ).

Lemma re_ok Γ :
  [ Γ |- ] ->
  [ %Γ |- ].
Proof with eauto using context_ok.
  intros.
  induction H...
  simpl.
  eapply u_ok...
  rewrite <- re_re; eauto.
Qed.