From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pad (Θ : context term) : context term -> Prop :=
| pad_O : pad Θ Θ
| pad_U Θ' m : pad Θ Θ' -> pad Θ (m :U Θ')
| pad_N Θ' : pad Θ Θ' -> pad Θ (_: Θ').

Inductive free : context term -> nat -> term -> context term -> Prop :=
| free_U Θ m l :
  l = length Θ ->
  free (Some (m, U) :: Θ) l m (Some (m, U) :: Θ)
| free_L Θ m l :
  l = length Θ ->
  free (Some (m, L) :: Θ) l m (None :: Θ)
| free_S Θ Θ' m n l :
  free Θ l m Θ' ->
  free (n :: Θ) l m (n :: Θ').

Inductive resolve : context term -> term -> term -> Prop :=
| resolve_var Θ x : 
  Θ |> U ->
  resolve Θ (Var x) (Var x)
| resolve_sort Θ s l :
  Θ |> U ->
  resolve Θ (Sort s l) (Sort s l)
| resolve_pi Θ A A' B B' s t :
  Θ |> U ->
  resolve Θ A A' ->
  resolve Θ B B' ->
  resolve Θ (Pi A B s t) (Pi A' B' s t)
| resolve_lam Θ A A' m m' s t :
  resolve [Θ] A A' ->
  resolve Θ m m' ->
  resolve Θ (Lam A m s t) (Lam A' m' s t)
| resolve_app Θ1 Θ2 Θ m m' n n' :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve Θ2 n n' ->
  resolve Θ (App m n) (App m' n')
| resolve_unit Θ :  
  Θ |> U ->
  resolve Θ Unit Unit
| resolve_it Θ : 
  Θ |> U ->
  resolve Θ It It
| resolve_sigma Θ A A' B B' s r t :
  Θ |> U ->
  resolve Θ A A' ->
  resolve Θ B B' ->
  resolve Θ (Sigma A B s r t) (Sigma A' B' s r t)
| resolve_pair Θ1 Θ2 Θ m m' n n' t :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve Θ2 n n' ->
  resolve Θ (Pair m n t) (Pair m' n' t)
| resolve_letin1 Θ1 Θ2 Θ m m' n n' :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve Θ2 n n' ->
  resolve Θ (LetIn1 m n) (LetIn1 m' n')
| resolve_letin2 Θ1 Θ2 Θ m m' n n' :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve Θ2 n n' ->
  resolve Θ (LetIn2 m n) (LetIn2 m' n')
| resovle_ptr Θ Θ' l m m' :
  free Θ l m Θ' ->
  resolve Θ' m m' ->
  resolve Θ (Ptr l) m'.

Inductive resolved : term -> Prop :=
| resolved_var x : 
  resolved (Var x)
| resolved_sort s l :
  resolved (Sort s l)
| resolved_pi A B s t :
  resolved A ->
  resolved B ->
  resolved (Pi A B s t)
| resolved_lam A m s t :
  resolved A ->
  resolved m ->
  resolved (Lam A m s t)
| resolved_app m n :
  resolved m ->
  resolved n ->
  resolved (App m n)
| resolved_unit :
  resolved Unit
| resolved_it :
  resolved It
| resolved_sigma A B s r t :
  resolved A ->
  resolved B ->
  resolved (Sigma A B s r t)
| resolved_pair m n t :
  resolved m ->
  resolved n ->
  resolved (Pair m n t)
| resolved_letin1 m n :
  resolved m ->
  resolved n ->
  resolved (LetIn1 m n)
| resolved_letin2 m n :
  resolved m ->
  resolved n ->
  resolved (LetIn2 m n).

Lemma pad_re Θ Θp : pad Θ Θp -> pad [Θ] [Θp].
Proof with eauto using pad. elim... Qed.

Lemma pad_mergeL Θ1 Θ2 Θ Θ1p : 
  pad Θ1 Θ1p -> Θ1 ∘ Θ2 => Θ -> 
  exists Θ2p Θp,
    pad Θ2 Θ2p /\ pad Θ Θp /\ Θ1p ∘ Θ2p => Θp.
Proof with eauto 6 using pad, merge.
  move=>pd. elim: pd Θ2 Θ=>{Θ1p}.
  move=>Θ2 Θ mrg.
  exists Θ2. exists Θ...
  move=>Θ' m pd ih Θ2 Θ /ih[Θ2p[Θp[pd1[pd2 mrg]]]].
  exists (m :U Θ2p). exists (m :U Θp)...
  move=>Θ' pd ih Θ2 Θ /ih[Θ2p[Θp[pd1[pd2 mrg]]]].
  exists (_: Θ2p). exists (_: Θp)...
Qed.

Lemma pad_mergeR Θ1 Θ2 Θ Θ2p : 
  pad Θ2 Θ2p -> Θ1 ∘ Θ2 => Θ -> 
  exists Θ1p Θp,
    pad Θ1 Θ1p /\ pad Θ Θp /\ Θ1p ∘ Θ2p => Θp.
Proof.
  move=>pd /merge_sym mrg.
  have[Θ1p[Θp[pd1[pd2 /merge_sym mrgx]]]]:=pad_mergeL pd mrg.
  exists Θ1p. exists Θp; eauto.
Qed.

Lemma pad_merge Θ1 Θ2 Θ Θp : 
  pad Θ Θp -> Θ1 ∘ Θ2 => Θ -> 
  exists Θ1p Θ2p,
    pad Θ1 Θ1p /\ pad Θ2 Θ2p /\ Θ1p ∘ Θ2p => Θp.
Proof with eauto 6 using pad, merge.
  move=>pd. elim: pd Θ1 Θ2=>{Θp}.
  move=>Θ1 Θ2 mrg.
  exists Θ1. exists Θ2...
  move=>Θ' m pd ih Θ1 Θ2 /ih[Θ1p[Θ2p[pd1[pd2 mrg]]]].
  exists (m :U Θ1p). exists (m :U Θ2p)...
  move=>Θ' pd ih Θ1 Θ2 /ih[Θ1p[Θ2p[pd1[pd2 mrg]]]].
  exists (_: Θ1p). exists (_: Θ2p)...
Qed.

Lemma resolve_resolved Θ m m' : resolve Θ m m' -> resolved m'.
Proof with eauto using resolved. elim=>{Θ m m'}... Qed.

Definition well_resolved Θ Γ m n A := 
  resolve Θ m n /\ Γ ⊢ n : A.

Lemma resolve_wkU Θ A A' m :
  resolve Θ A A' -> resolve (m :U Θ) A A'.
Proof with eauto using resolve, key, merge.
  move=>rs. elim: rs m=>{Θ A A'}...
  move=>Θ Θ' l m m' fr rs ih n.
  have{}ih:=ih n.
  econstructor...
  econstructor...
Qed.

Lemma resolve_wkN Θ A A' :
  resolve Θ A A' -> resolve (_: Θ) A A'.
Proof with eauto using resolve, key, merge.
  move=>rs. elim: rs=>{Θ A A'}...
  move=>Θ Θ' l m m' fr rs ih.
  econstructor...
  econstructor...
Qed.

Lemma resolve_pad Θ Θ' A A' :
  pad Θ Θ' -> resolve Θ A A' -> resolve Θ' A A'. 
Proof with eauto using resolve_wkU, resolve_wkN.
  move=>pd. elim: pd A A'=>{Θ'}...
Qed.

Lemma resolve_type_refl Θ Γ m A : Γ ⊢ m : A -> resolve [Θ] m m.
Proof with eauto using resolve, re_pure, merge_re_id.
  elim=>//{Γ m A}...
  move=>Γ A B m s t i k tyP rs tym rsm.
  constructor... inv rs. rewrite<-re_invo...
Qed.

Lemma resolve_type_id Θ Γ m n A : 
  Γ ⊢ m : A -> resolve Θ m n -> m = n.
Proof with eauto using resolve, re_pure, merge_re_id, re_pure.
  move=>ty. elim: ty Θ n=>//{Γ m A}.
  move=>Γ s l k Θ n rs. inv rs...
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ n rs. inv rs.
    erewrite ihA... erewrite ihB...
  move=>Γ x A s hs Θ n rs. inv rs...
  move=>Γ A B m s t i k tyP ihP tym ihm Θ n rs. inv rs.
    have[r[l[tyA tyB]]]:=pi_inv _ _ _ _ _ _ tyP.
    have/ihP[->]: resolve[Θ] (Pi A B s t) (Pi A' B s t).
    constructor...
    apply: resolve_type_refl...
    erewrite ihm...
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn Θ x rs. inv rs.
    erewrite ihm... erewrite ihn...
  move=>Γ k Θ n rs. inv rs...
  move=>Γ k Θ n rs. inv rs...
  move=>Γ A B s r t i le k tyA ihA tyB ihB Θ n rs. inv rs.
    erewrite ihA... erewrite ihB... 
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg 
    tyS ihS tym ihm tyn ihn Θ x rs. inv rs.
    erewrite ihm... erewrite ihn...
  move=>Γ1 Γ2 Γ m n A mrg tym ihm tyn ihn Θ x rs. inv rs.
    erewrite ihm... erewrite ihn...
  move=>Γ1 Γ2 Γ A B C m n s r t k x i le key mrg 
    tym ihm tyC ihC tyn ihn Θ z rs. inv rs.
    erewrite ihm... erewrite ihn...
Qed.

Lemma free_length Θ l n Θ' : free Θ l n Θ' -> l <= length Θ. 
Proof.
  elim=>{Θ l n Θ'}.
  move=>Θ m l->//=.
  move=>Θ m l->//=.
  move=>Θ Θ' m n l fr leq//=.
  apply: leq_trans.
  exact: leq.
  eauto.
Qed.

Lemma free_inv Θ Θ' m n t : 
  free (m :{t} Θ) (length Θ) n Θ' -> 
  m = n /\ 
  match t with
  | U => m :{t} Θ
  | L => _: Θ
  end = Θ'.
Proof.
  elim: Θ Θ' m n=>//=.
  move=>Θ' m n fr. inv fr=>//. inv H4.
  move=>m Θ ih Θ' m0 n fr=>//. inv fr=>//.
  exfalso.
  inv H4.
  have:(length Θ).+1 - (length Θ) = (length Θ) - (length Θ).
  by rewrite H5.
  rewrite subnn.
  rewrite subSnn=>//.
  have:(length Θ).+1 - (length Θ) = (length Θ) - (length Θ).
  by rewrite H5.
  rewrite subnn.
  rewrite subSnn=>//.
  move/free_length in H5.
  unfold leq in H5.
  rewrite subSnn in H5.
  move/eqnP in H5.
  inv H5.
Qed.