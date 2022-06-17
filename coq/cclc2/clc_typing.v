From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ m : A : s" 
  (at level 50, m, A, s at next level).

Inductive clc_type : context term -> term -> term -> sort -> Prop :=
| clc_axiom Γ s :
  Γ |> U ->
  Γ ⊢ Sort s : Sort U : U
| clc_pi Γ A B s r t :
  Γ |> U ->
  Γ ⊢ A : Sort s : U ->
  [A :{s} Γ] ⊢ B : Sort r : U ->
  Γ ⊢ Pi A B s r t : Sort t : U
| clc_var Γ x A s :
  has Γ x s A ->
  Γ ⊢ Var x : A : s
| clc_lam Γ A B m s r t :
  Γ |> t ->
  [Γ] ⊢ Pi A B s r t : Sort t : U ->
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
  Γ ⊢ Unit : Sort U : U
| clc_it Γ :
  Γ |> U ->
  Γ ⊢ It : Unit : U
| clc_either Γ :
  Γ |> U ->
  Γ ⊢ Either : Sort U : U
| clc_left Γ :
  Γ |> U ->
  Γ ⊢ Left : Either : U
| clc_right Γ :
  Γ |> U ->
  Γ ⊢ Right : Either : U
| clc_sigma Γ A B s r t :
  s ⋅ r ≤ t ->
  Γ |> U ->
  Γ ⊢ A : Sort s : U ->
  [A :{s} Γ] ⊢ B : Sort r : U ->
  Γ ⊢ Sigma A B s r t : Sort t : U
| clc_pair Γ1 Γ2 Γ A B m n s r t :
  Γ1 |> s ->
  Γ2 |> r ->
  Γ1 ∘ Γ2 => Γ ->
  [Γ] ⊢ Sigma A B s r t : Sort t : U ->
  Γ1 ⊢ m : A : s ->
  Γ2 ⊢ n : B.[m/] : r ->
  Γ ⊢ Pair m n t : Sigma A B s r t : t
| clc_case Γ1 Γ2 Γ m n1 n2 A s t :
  Γ1 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Either : U ->
  [Either :{s} Γ2] ⊢ A : Sort t : U ->
  Γ2 ⊢ n1 : A.[Left/] : t ->
  Γ2 ⊢ n2 : A.[Right/] : t ->
  Γ ⊢ Case m n1 n2 : A.[m/] : t
| clc_letin1 Γ1 Γ2 Γ m n A s :
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Unit : U ->
  Γ2 ⊢ n : A : s ->
  Γ ⊢ LetIn1 m n : A : s
| clc_letin2 Γ1 Γ2 Γ A B C m n s r t k x :
  t ≤ k ->
  Γ1 |> k ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Sigma A B s r t : t ->
  [Sigma A B s r t :{k} Γ2] ⊢ C : Sort x : U ->
  B :{r} A :{s} Γ2 ⊢ n : C.[Pair (Var 1) (Var 0) t .: ren (+2)] : x ->
  Γ ⊢ LetIn2 m n : C.[m/] : x
| clc_main Γ :
  Γ |> U ->
  Γ ⊢ Main : Sort L : U
| clc_proto Γ :
  Γ |> U ->
  Γ ⊢ Proto : Sort U : U
| clc_stop Γ r :
  Γ |> U ->
  Γ ⊢ Stop r : Proto : U
| clc_act Γ r A B s :
  Γ |> U ->
  Γ ⊢ A : Sort s : U ->
  [A :{s} Γ] ⊢ B : Proto : U ->
  Γ ⊢ Act r A B s : Proto : U
| clc_ch Γ r A :
  Γ |> U ->
  Γ ⊢ A : Proto : U ->
  Γ ⊢ Ch r A : Sort L : U
| clc_fork Γ1 Γ2 r1 r2 Γ m n A B s t :
  Γ1 ∘ Γ2 => Γ ->
  r1 = ~~r2 ->
  [Γ1] ⊢ Ch r1 A : Sort L : U ->
  [Γ2] ⊢ Ch r2 A : Sort L : U ->
  Γ1 ⊢ m : Main : L ->
  Γ2 ⊢ n : Pi (Ch r2 A) B L s t : t ->
  Γ ⊢ Fork m n : Sigma (Ch r1 A) Main L L L : L
| clc_recv Γ r1 r2 A B m s :
  addb r1 r2 = false ->
  Γ ⊢ m : Ch r1 (Act r2 A B s) : L ->
  Γ ⊢ Recv m : Sigma A (Ch r1 B) s L L : L
| clc_send Γ r1 r2 A B m s :
  addb r1 r2 = true ->
  Γ ⊢ m : Ch r1 (Act r2 A B s) : L ->
  Γ ⊢ Send m : Pi A (Ch r1 B) s L L : L
| clc_wait Γ r1 r2 m :
  addb r1 r2 = false ->
  Γ ⊢ m : Ch r1 (Stop r2) : L ->
  Γ ⊢ Wait m : Unit : U
| clc_close Γ r1 r2 m :
  addb r1 r2 = true ->
  Γ ⊢ m : Ch r1 (Stop r2) : L ->
  Γ ⊢ Close m : Unit : U
| clc_conv Γ A B m s :
  A === B ->
  Γ ⊢ m : A : s ->
  [Γ] ⊢ B : Sort s : U ->
  Γ ⊢ m : B : s
where "Γ ⊢ m : A : s" := (clc_type Γ m A s).

Inductive ok : context term -> Prop :=
| nil_ok :
  ok nil
| ty_ok Γ A s :
  ok Γ ->
  [Γ] ⊢ A : Sort s : U ->
  ok (A :{s} Γ)
| n_ok Γ :
  ok Γ ->
  ok (_: Γ).

Lemma re_ok Γ : ok Γ -> ok [Γ].
Proof with eauto using ok.
  elim=>{Γ}...
  move=>Γ A [|] wf1 wf2 ty//=.
  apply: ty_ok... rewrite<-re_invo; eauto.
  apply: n_ok...
Qed.
