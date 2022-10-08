From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export clc_confluence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ m : A" 
  (at level 50, m, A at next level).

Inductive clc_type : context term -> term -> term -> Prop :=
| clc_axiom Γ s :
  Γ |> U ->
  Γ ⊢ Sort s : Sort U
| clc_pi Γ A B s r t :
  Γ |> U ->
  Γ ⊢ A : Sort s ->
  [A :{s} Γ] ⊢ B : Sort r ->
  Γ ⊢ Pi A B s t : Sort t
| clc_var Γ x A s :
  has Γ x s A ->
  Γ ⊢ Var x : A
| clc_lam Γ A B m s t :
  Γ |> t ->
  [Γ] ⊢ Pi A B s t : Sort t ->
  A :{s} Γ ⊢ m : B ->
  Γ ⊢ Lam A m s t : Pi A B s t
| clc_app Γ1 Γ2 Γ A B m n s t :
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Pi A B s t ->
  Γ2 ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| clc_fix Γ A m :
  Γ |> U ->
  Γ ⊢ A : Sort U ->
  A :U Γ ⊢ m : A.[ren (+1)] ->
  Γ ⊢ Fix A m : A
| clc_unit Γ :
  Γ |> U ->
  Γ ⊢ Unit : Sort U
| clc_it Γ :
  Γ |> U ->
  Γ ⊢ It : Unit
| clc_either Γ :
  Γ |> U ->
  Γ ⊢ Either : Sort U
| clc_left Γ :
  Γ |> U ->
  Γ ⊢ Left : Either
| clc_right Γ :
  Γ |> U ->
  Γ ⊢ Right : Either
| clc_sigma Γ A B s r t :
  s ⋅ r ≤ t ->
  Γ |> U ->
  Γ ⊢ A : Sort s ->
  [A :{s} Γ] ⊢ B : Sort r ->
  Γ ⊢ Sigma A B s r t : Sort t
| clc_pair Γ1 Γ2 Γ A B m n s r t :
  Γ1 |> s ->
  Γ2 |> r ->
  Γ1 ∘ Γ2 => Γ ->
  [Γ] ⊢ Sigma A B s r t : Sort t ->
  Γ1 ⊢ m : A ->
  Γ2 ⊢ n : B.[m/] ->
  Γ ⊢ Pair m n t : Sigma A B s r t
| clc_case Γ1 Γ2 Γ m n1 n2 A s t :
  Γ1 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Either ->
  [Either :{s} Γ2] ⊢ A : Sort t ->
  Γ2 ⊢ n1 : A.[Left/] ->
  Γ2 ⊢ n2 : A.[Right/] ->
  Γ ⊢ Case A m n1 n2 : A.[m/]
| clc_letin1 Γ1 Γ2 Γ m n A s t :
  Γ1 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Unit ->
  [Unit :{s} Γ2] ⊢ A : Sort t ->
  Γ2 ⊢ n : A.[It/] ->
  Γ ⊢ LetIn1 A m n : A.[m/]
| clc_letin2 Γ1 Γ2 Γ A B C m n s r t k x :
  t ≤ k ->
  Γ1 |> k ->
  Γ1 ∘ Γ2 => Γ ->
  Γ1 ⊢ m : Sigma A B s r t ->
  [Sigma A B s r t :{k} Γ2] ⊢ C : Sort x ->
  B :{r} A :{s} Γ2 ⊢ n : C.[Pair (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn2 C m n : C.[m/]
| clc_main Γ :
  Γ |> U ->
  Γ ⊢ Main : Sort L
| clc_proto Γ :
  Γ |> U ->
  Γ ⊢ Proto : Sort U
| clc_stop Γ r :
  Γ |> U ->
  Γ ⊢ Stop r : Proto
| clc_act Γ r A B s :
  Γ |> U ->
  Γ ⊢ A : Sort s ->
  [A :{s} Γ] ⊢ B : Proto ->
  Γ ⊢ Act r A B s : Proto
| clc_ch Γ r A :
  Γ |> U ->
  Γ ⊢ A : Proto ->
  Γ ⊢ Ch r A : Sort L
| clc_fork Γ1 Γ2 r1 r2 Γ m n A B t :
  Γ1 ∘ Γ2 => Γ ->
  r1 = ~~r2 ->
  [Γ] ⊢ A : Proto ->
  Γ1 ⊢ m : Main ->
  Γ2 ⊢ n : Pi (Ch r2 A) B L t ->
  Γ ⊢ Fork m n : Sigma (Ch r1 A) Main L L L
| clc_recv Γ r1 r2 A B m s :
  addb r1 r2 = false ->
  Γ ⊢ m : Ch r1 (Act r2 A B s) ->
  Γ ⊢ Recv m : Sigma A (Ch r1 B) s L L
| clc_send Γ r1 r2 A B m s :
  addb r1 r2 = true ->
  Γ ⊢ m : Ch r1 (Act r2 A B s) ->
  Γ ⊢ Send m : Pi A (Ch r1 B) s L
| clc_wait Γ r1 r2 m :
  addb r1 r2 = false ->
  Γ ⊢ m : Ch r1 (Stop r2) ->
  Γ ⊢ Wait m : Unit
| clc_close Γ r1 r2 m :
  addb r1 r2 = true ->
  Γ ⊢ m : Ch r1 (Stop r2) ->
  Γ ⊢ Close m : Unit
| clc_conv Γ A B m s :
  A === B ->
  Γ ⊢ m : A ->
  [Γ] ⊢ B : Sort s ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (clc_type Γ m A).

Inductive ok : context term -> Prop :=
| nil_ok :
  ok nil
| ty_ok Γ A s :
  ok Γ ->
  [Γ] ⊢ A : Sort s ->
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
