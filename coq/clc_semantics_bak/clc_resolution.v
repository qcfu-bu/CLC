From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value : term -> Prop :=
| value_sort s l :
  value (Sort s l)
| value_pi A B s r t :
  value (Pi A B s r t)
| value_lam A m s t :
  value (Lam A m s t)
| value_unit :
  value Unit
| value_it :
  value It
| value_sigma A B s r t :
  value (Sigma A B s r t)
| value_pair m n t :
  value (Pair m n t).

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
| resolve_pi Θ A A' B B' s r t :
  Θ |> U ->
  resolve Θ A A' ->
  resolve Θ B B' ->
  resolve Θ (Pi A B s r t) (Pi A' B' s r t)
| resolve_lam Θ A A' m m' s t :
  Θ |> t ->
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
  Θ |> t ->
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
| resolve_ptr Θ Θ' l m m' :
  free Θ l m Θ' ->
  resolve Θ' m m' ->
  resolve Θ (Ptr l) m'.

Inductive resolved : term -> Prop :=
| resolved_var x : 
  resolved (Var x)
| resolved_sort s l :
  resolved (Sort s l)
| resolved_pi A B s r t :
  resolved A ->
  resolved B ->
  resolved (Pi A B s r t)
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

Inductive well_resolved : 
  context term -> term -> term -> term -> sort -> Prop := 
| Well_resolved Θ m n A t :
  resolve Θ m n -> nil ⊢ n : A : t -> well_resolved Θ m n A t.

Lemma resolve_wkU Θ A A' m :
  resolve Θ A A' -> resolve (m :U Θ) A A'.
Proof with eauto using resolve, key, merge.
  move=>rs. elim: rs m=>{Θ A A'}...
  move=>Θ A A' B B' s []...
  move=>Θ1 Θ2 Θ m m' n n' []...
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

Lemma resolve_type_refl Θ Γ m A s : Γ ⊢ m : A : s -> resolve [Θ] m m.
Proof with eauto using resolve, re_pure, merge_re_id.
  elim=>//{Γ m A s}...
  move=>Γ A B m s r t i k tyP rsP tym rsm.
  constructor... 
  apply: re_sort.
  inv rsP. rewrite<-re_invo...
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg tyS rsS tym rsm tyn rsn.
  econstructor... 
  apply: re_sort.
Qed.

Lemma resolve_type_id Θ Γ m n A s : 
  Γ ⊢ m : A : s -> resolve Θ m n -> m = n.
Proof with eauto using resolve, re_pure, merge_re_id, re_pure.
  move=>ty. elim: ty Θ n=>//{Γ m A s}.
  move=>Γ s l k Θ n rs. inv rs...
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ n rs. inv rs.
    erewrite ihA... erewrite ihB...
  move=>Γ x A s hs Θ n rs. inv rs...
  move=>Γ A B m s r t i k tyP ihP tym ihm Θ n rs. inv rs.
    have[l[tyA[_ tyB]]]:=pi_inv _ _ _ _ _ _ _ _ tyP.
    have/ihP[->]: resolve[Θ] (Pi A B s r t) (Pi A' B s r t).
    constructor...
    apply: resolve_type_refl...
    erewrite ihm...
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn Θ x rs. inv rs.
    erewrite ihm... erewrite ihn...
  move=>Γ k Θ n rs. inv rs...
  move=>Γ k Θ n rs. inv rs...
  move=>Γ A B s r t i le k tyA ihA tyB ihB Θ n rs. inv rs.
    erewrite ihA... erewrite ihB... 
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg 
    tyS ihS tym ihm tyn ihn Θ x rs. inv rs.
    erewrite ihm... erewrite ihn...
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn ihn Θ x rs. inv rs.
    erewrite ihm... erewrite ihn...
  move=>Γ1 Γ2 Γ A B C m n s r t k x i le key mrg 
    tym ihm tyC ihC tyn ihn Θ z rs. inv rs.
    erewrite ihm... erewrite ihn...
Qed.

Lemma free_length Θ l n Θ' : free Θ l n Θ' -> l < length Θ. 
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
  have le :length Θ < (length Θ).+2 by eauto.
  have h:= leq_trans H5 le.
  unfold leq in h.
  rewrite subSnn in h.
  move/eqnP in h; inv h.
Qed.

Lemma free_empty Θ Θ' n : ~free (_: Θ) (length Θ) n Θ'.
Proof.
  elim: Θ Θ' n=>//=.
  move=>Θ' n fr. inv fr. inv H4.
  move=>m Θ ih Θ' n fr=>//. inv fr=>//.
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
  have le :length Θ < (length Θ).+2 by eauto.
  have h:= leq_trans H5 le.
  unfold leq in h.
  rewrite subSnn in h.
  move/eqnP in h; inv h.
Qed.

Lemma free_merge Θ1 Θ2 Θ3 Θ l m :
  free Θ1 l m Θ3 -> Θ1 ∘ Θ2 => Θ ->
    exists Θ4, free Θ l m Θ4 /\ Θ3 ∘ Θ2 => Θ4.
Proof with eauto using free, merge.
  move=>fr. elim: fr Θ2 Θ=>{Θ1 Θ3 l m}.
  move=>Θ m l e Θ2 Θ0 mrg. inv mrg.
  exists (m :U Γ). split...
  econstructor.
  have[->_]//=:=merge_length H3.
  move=>Θ m l e Θ2 Θ0 mrg. inv mrg.
  exists (_: Γ). split...
  econstructor.
  have[->_]//:=merge_length H3.
  move=>Θ Θ' m n l fr ih Θ2 Θ0 mrg. inv mrg.
  have[Θ4[fr0 mrg]]:=ih _ _ H3. 
    exists (m0 :U Θ4). split...
  have[Θ4[fr0 mrg]]:=ih _ _ H3. 
    exists (m0 :L Θ4). split...
  have[Θ4[fr0 mrg]]:=ih _ _ H3. 
    exists (m0 :L Θ4). split...
  have[Θ4[fr0 mrg]]:=ih _ _ H3. 
    exists (_: Θ4). split...
Qed.

Lemma free_pure Θ Θ' m l : free Θ l m Θ' -> Θ |> U -> Θ' |> U.
Proof.
  elim=>//{Θ Θ' m l}.
  move=>Θ m l e k. inv k.
  move=>Θ Θ' m n l fr ih mrg. inv mrg.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma free_subset Θ Θ1 Θ2 Θ' Θ1' l m n :
  Θ1 ∘ Θ2 => Θ ->free Θ l m Θ' -> free Θ1 l n Θ1' ->  m = n /\ Θ1' ∘ Θ2 => Θ'.
Proof with eauto 6 using merge.
  move=>mrg. elim: mrg l m n Θ' Θ1'=>{Θ Θ1 Θ2}.
  move=>l m n G1 G2 fr. inv fr.
  move=>G1 G2 G m mrg ih l n x G3 G4 fr1 fr2.
  { have[e1 e2]:=merge_length mrg.
    inv fr1; inv fr2...
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4. 
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
  move=>G1 G2 G m mrg ih l n x G3 G4 fr1 fr2.
  { have[e1 e2]:=merge_length mrg.
    inv fr1; inv fr2...
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4. 
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
  move=>G1 G2 G m mrg ih l n x G3 G4 fr1 fr2.
  { have[e1 e2]:=merge_length mrg.
    inv fr1; inv fr2.
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4. 
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
  move=>G1 G2 G mrg ih l m n G3 G4 fr1 fr2.
  { inv fr1; inv fr2... 
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
Qed.

Lemma resolve_merge_pure Θ1 Θ2 Θ A A' :
  resolve Θ1 A A' -> Θ1 ∘ Θ2 => Θ -> Θ2 |> U -> resolve Θ A A'.
Proof with eauto using 
  resolve, merge_pure_pure, key, resolve_wkU, resolve_wkN.
  move=>rsA. elim: rsA Θ2 Θ=>{Θ1 A A'}...
  move=>Θ A A' m m' s t k1 rsA ihA rsm ihm Θ2 Θ0 mrg k2.
  { constructor...
    destruct t...
    apply: key_impure.
    have[e1[e2 e3]]:=merge_re_re mrg.
    apply: ihA.
    rewrite<-e2.
    apply: merge_re_id.
    apply: re_pure. }
  move=>Θ1 Θ2 Θ m m' n n' mrg1 rsm ihm rsn ihn Θ0 Θ3 mrg2 k.
  { have[G[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm; eauto.
    eauto. }
  move=>Θ1 Θ2 Θ m m' n n' t k1 mrg1 rsm ihm rsn ihn Θ0 Θ3 mrg2 k2.
  { have[G[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    destruct t...
    apply: key_impure.
    apply: mrg4.
    apply: ihm; eauto.
    eauto. }
  move=>Θ1 Θ2 Θ m m' n n' mrg1 rsm ihm rsn ihn Θ0 Θ3 mrg2 k.
  { have[G[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm; eauto.
    eauto. }
  move=>Θ1 Θ2 Θ m m' n n' mrg1 rsm ihm rsn ihn Θ0 Θ3 mrg2 k.
  { have[G[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm; eauto.
    eauto. }
  move=>Θ Θ' l m m' fr rs ih Θ2 Θ0 mrg k.
  { have[G[fr' mrg']]:=free_merge fr mrg.
    econstructor.
    apply: fr'.
    apply: ih.
    apply: mrg'.
    eauto. }
Qed.

Lemma resolve_free Θ1 Θ2 Θ Θ' l m n :
  free Θ l n Θ' -> resolve Θ1 (Ptr l) m -> Θ1 ∘ Θ2 => Θ -> 
  exists Θ1', Θ1' ∘ Θ2 => Θ' /\ resolve Θ1' n m.
Proof with eauto using merge.
  intros.
  inv H0.
  have [e mrg]:=free_subset H1 H H3; subst.
  exists Θ'0.
  split...
Qed.

Inductive nf : nat -> term -> Prop :=
| nf_var i x : 
  x < i ->
  nf i (Var x)
| nf_sort i s l :
  nf i (s @ l)
| nf_pi i A B s r t :
  nf i A ->
  nf i.+1 B ->
  nf i (Pi A B s r t)
| nf_lam i A m s t :
  nf i A ->
  nf i.+1 m ->
  nf i (Lam A m s t)
| nf_app i m n :
  nf i m ->
  nf i n ->
  nf i (App m n)
| nf_unit i :
  nf i Unit
| nf_it i :
  nf i It
| nf_sigma i A B s r t :
  nf i A ->
  nf i.+1 B ->
  nf i (Sigma A B s r t)
| nf_pair i m n t :
  nf i m ->
  nf i n ->
  nf i (Pair m n t)
| nf_letin1 i m n :
  nf i m ->
  nf i n ->
  nf i (LetIn1 m n)
| nf_letin2 i m n :
  nf i m ->
  nf i.+2 n ->
  nf i (LetIn2 m n)
| nf_ptr i l :
  nf i (Ptr l).

Inductive wr_env : context term -> Prop :=
| wr_nil : wr_env nil
| wr_cons Θ s i :
  wr_env Θ ->
  wr_env (s @ i :U Θ)
| wr_pi Θ A B s r t :
  nf 0 A ->
  nf 1 B ->
  wr_env Θ ->
  wr_env (Pi A B s r t :U Θ)
| wr_lam Θ A m s t :
  nf 0 A ->
  nf 1 m ->
  wr_env Θ ->
  wr_env (Lam A m s t :{t} Θ)
| wr_unit Θ :
  wr_env Θ ->
  wr_env (Unit :U Θ)
| wr_it Θ :
  wr_env Θ ->
  wr_env (It :U Θ)
| wr_env_sigma Θ A B s r t :
  nf 0 A ->
  nf 1 B ->
  wr_env Θ ->
  wr_env (Sigma A B s r t :U Θ)
| wr_pair Θ m n t :
  nf 0 m ->
  nf 0 n ->
  wr_env Θ ->
  wr_env (Pair m n t :{t} Θ)
| wr_N Θ :
  wr_env Θ ->
  wr_env (_: Θ).

Lemma nf_typing m A s Γ : 
  Γ ⊢ m : A : s -> nf (length Γ) m.
Proof with eauto using nf.
  elim=>//{Γ m A s}...
  move=>Γ A B [|]//= r t i k _ ihA _ ihB.
    constructor... rewrite re_length...
    constructor... rewrite re_length...
  move=>Γ x A s hs.
    constructor. apply: has_length...
  move=>Γ A B m [|]//= r t i k tyP nfP tym nfm.
    inv nfP. constructor... rewrite re_length...
    inv nfP. constructor... rewrite re_length...
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym nfm tyn nfn.
    have[e1 e2]:=merge_length mrg. 
    constructor... rewrite<-e1... rewrite<-e2...
  move=>Γ A B [|]//= r t i le k tyA nfA tyB nfB.
    constructor... rewrite re_length...
    constructor... rewrite re_length...
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg tyS nfS tym nfm tyn nfn.
    have[e1 e2]:=merge_length mrg. 
    constructor. rewrite<-e1... rewrite<-e2...
  move=>Γ1 Γ2 Γ m n A s mrg tym nfm tyn nfn.
    have[e1 e2]:=merge_length mrg. 
    constructor. rewrite<-e1... rewrite<-e2...
  move=>Γ1 Γ2 Γ A B C m n [|] [|]//= t k x i le key mrg 
    tym nfm tyC nfC tyn nfn;
    have[e1 e2]:=merge_length mrg;
    constructor;
    (try solve[rewrite<-e1; eauto]) ||
    (try solve[rewrite<-e2; eauto]).
Qed.

Lemma wr_env_re Θ : wr_env Θ -> wr_env [Θ].
Proof with eauto using wr_env.
  elim=>{Θ}...
  move=>Θ A m s [|] nfA nfm wr ih//=...
  move=>Θ m n [|] nfm nfn wr ih//=...
Qed.

Lemma free_wr_nf Θ l m Θ' :
  free Θ l m Θ' -> wr_env Θ -> nf 0 m.
Proof with eauto using nf.
  elim=>//{Θ l m Θ'}.
  move=>Θ m l e wr. inv wr...
  move=>Θ m l e wr. inv wr...
  move=>Θ Θ' m n l fr ih wr. inv wr...
Qed.

Lemma wr_merge Θ1 Θ2 Θ :
  Θ1 ∘ Θ2 => Θ -> wr_env Θ1 -> wr_env Θ2 -> wr_env Θ.
Proof with eauto using wr_env.
  elim=>{Θ1 Θ2 Θ}...
  move=>Θ1 Θ2 Θ m mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
  move=>Θ1 Θ2 Θ m mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
  move=>Θ1 Θ2 Θ m mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
  move=>Θ1 Θ2 Θ mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
Qed.

Lemma wr_merge_inv Θ1 Θ2 Θ : 
  Θ1 ∘ Θ2 => Θ -> wr_env Θ -> wr_env Θ1 /\ wr_env Θ2.
Proof with eauto using wr_env.
  elim...
  move=>Γ1 Γ2 Γ m mrg ih wr. inv wr.
    move:H0=>/ih[wr1 wr2]...
    move:H3=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
    move:H0=>/ih[wr1 wr2]...
    move:H0=>/ih[wr1 wr2]...
    move:H3=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
  move=>Γ1 Γ2 Γ m mrg ih wr. inv wr.
    move:H4=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
  move=>Γ1 Γ2 Γ m mrg ih wr. inv wr.
    move:H4=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
  move=>Γ1 Γ2 Γ mrg ih wr. inv wr.
    move:H0=>/ih[wr1 wr2]...
Qed.

Lemma free_wr Θ Θ' l m :
  free Θ l m Θ' -> wr_env Θ -> wr_env Θ'.
Proof with eauto using wr_env.
  elim=>{Θ l m Θ'}; eauto.
  move=>Θ m l e wr. inv wr...
  move=>Θ Θ' m n l fr ih wr.
  inv wr...
Qed.

Lemma nf_weaken i j m : nf i m -> i <= j -> nf j m.
Proof with eauto using nf.
  move=>nfm. elim: nfm j=>{m i}...
  move=>i x l1 j l2.
  constructor.
  apply: leq_trans...
Qed.

Lemma resolve_wr_nfi Θ m m' i : 
  resolve Θ m m' -> wr_env Θ -> nf i m' -> nf i m.
Proof with eauto using nf, wr_env_re.
  move=>rs. elim: rs i=>{Θ m m'}...
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i wr nfP. inv nfP...
  move=>Θ A A' m m' s t k rsA ihA rsm ihm i wr nfL. inv nfL... 
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i wr nfA. 
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfA... }
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i wr nfS. inv nfS...
  move=>Θ1 Θ2 Θ m m' n n' t k mrg rsm ihm rsn ihn i wr nfP.
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfP... }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i wr nfL. 
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfL... }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i wr nfL.
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfL... }
Qed.

Lemma resolve_wr_nfi' Θ m m' i : 
  resolve Θ m m' -> wr_env Θ -> nf i m -> nf i m'.
Proof with eauto using nf, wr_env_re.
  move=>rs. elim: rs i=>{Θ m m'}...
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i wr nfP. inv nfP...
  move=>Θ A A' m m' s t k rsA ihA rsm ihm i wr nfL. inv nfL... 
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i wr nfA. 
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfA... }
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i wr nfS. inv nfS...
  move=>Θ1 Θ2 Θ m m' n n' t k mrg rsm ihm rsn ihn i wr nfP.
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfP... }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i wr nfL. 
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfL... }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i wr nfL.
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfL... }
  move=>Θ Θ' l m m' fr rs ih i wr nfP.
  { apply: ih...
    apply: free_wr...
    have n0:=free_wr_nf fr wr.
    apply: nf_weaken... }
Qed.

Lemma free_wr_ptr Θ Θ' l i :
  free Θ l (Ptr i) Θ' -> wr_env Θ -> False.
Proof.
  move e:(Ptr i)=>m fr. elim: fr i e=>{Θ Θ' l m}.
  move=>Θ m l e1 i e2 wr; subst. inv wr.
  move=>Θ m l e1 i e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih i e wr; subst.
  inv wr; apply: ih; eauto.
Qed.

Lemma free_wr_sort Θ Θ' l s i :
  free Θ l (s @ i) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(s @ i)=>m fr. elim: fr s i e=>//{Θ Θ' l m}.
  move=>Θ m l e1 s i e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih s i e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_pi Θ Θ' l A B s r t :
  free Θ l (Pi A B s r t) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Pi A B s r t)=>m fr. elim: fr A B s r t e=>//{Θ Θ' l m}.
  move=>Θ m l e1 A B s r t e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih A B s r t e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_var Θ Θ' l x :
  free Θ l (Var x) Θ' -> wr_env Θ -> False.
Proof.
  move e:(Var x)=>m fr. elim: fr x e=>//{Θ Θ' l m}.
  move=>Θ m l e1 x e2 wr; subst. inv wr.
  move=>Θ m l e1 x e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih x e wr; subst.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_lam Θ Θ' l A m s :
  free Θ l (Lam A m s U) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Lam A m s U)=>n fr. elim: fr A m s e=>//{Θ Θ' l n}.
  move=>Θ m l e1 A n s e2 wr; subst. inv wr. inv H4.
  move=>Θ Θ' m n l fr ih A n0 s e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_unit Θ Θ' l : free Θ l Unit Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Unit)=>n fr. elim: fr e=>//{Θ Θ' l n}.
  move=>Θ m l e1 e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_it Θ Θ' l : free Θ l It Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(It)=>n fr. elim: fr e=>//{Θ Θ' l n}.
  move=>Θ m l e1 e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_sigma Θ Θ' l A B s r t :
  free Θ l (Sigma A B s r t) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Sigma A B s r t)=>m fr. elim: fr A B s r t e=>//{Θ Θ' l m}.
  move=>Θ m l e1 A B s r t e2 wr; subst. inv wr.
  move=>Θ Θ' m n l fr ih A B s r t e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_pair Θ Θ' l m n :
  free Θ l (Pair m n U) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Pair m n U)=>x fr. elim: fr m n e=>//{Θ Θ' l x}.
  move=>Θ m l e1 m0 n e2 wr; subst. inv wr. inv H3.
  move=>Θ Θ' m n l fr ih m0 n0 e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma resolve_sort_inv Θ m s i :
  wr_env Θ -> resolve Θ m (s @ i) -> Θ |> U.
Proof.
  move e:(s @ i)=>n wr rs.
  elim: rs s i wr e=>//{Θ m n}.
  move=>Θ Θ' l m m' fr rs ih s i wr e; subst.
  destruct m; inv rs.
  have->//:=free_wr_sort fr wr.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_pi_inv Θ m A B s r t :
  wr_env Θ -> resolve Θ m (Pi A B s r t) -> Θ |> U.
Proof.
  move e:(Pi A B s r t)=>n wr rs.
  elim: rs A B s r t wr e=>//{Θ m n}.
  move=>Θ Θ' l m m' fr rsm ihm A B s r t wr e; subst.
  destruct m; inv rsm.
  have->//:=free_wr_pi fr wr.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_var_inv Θ m x :
  wr_env Θ -> resolve Θ m (Var x) -> Θ |> U.
Proof.
  move e:(Var x)=>n wr rs.
  elim: rs x e wr=>//{Θ m n}.
  move=>Θ Θ' l n n' fr rs ih x e wr; subst.
  destruct n; inv rs.
  exfalso. apply: free_wr_var; eauto.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_lam_inv Θ m A n s t : 
  wr_env Θ -> resolve Θ m (Lam A n s t) -> Θ |> t.
Proof.
  move e:(Lam A n s t)=>v wr rs.
  elim: rs A n s t e wr=>//{Θ m v}.
  move=>Θ A A' m m' s t k rsA ihA rsm ihm A0 n s0 t0
    [e1 e2 e3 e4] wr; subst; eauto.
  move=>Θ Θ' l m m' fr rsm ihm A n s t e wr; subst.
  destruct m; inv rsm.
  destruct t.
  have->//:=free_wr_lam fr wr.
  apply: key_impure.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_unit_inv Θ m :
  wr_env Θ -> resolve Θ m Unit -> Θ |> U.
Proof.
  move e:(Unit)=>n wr rs. elim: rs wr e=>//{Θ m n}.
  move=>Θ Θ' l m m' fr rs ih wr e; subst.
  destruct m; inv rs.
  have->//:=free_wr_unit fr wr.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_it_inv Θ m :
  wr_env Θ -> resolve Θ m It -> Θ |> U.
Proof.
  move e:(It)=>n wr rs. elim: rs wr e=>//{Θ m n}.
  move=>Θ Θ' l m m' fr rs ih wr e; subst.
  destruct m; inv rs.
  have->//:=free_wr_it fr wr.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_sigma_inv Θ m A B s r t :
  wr_env Θ -> resolve Θ m (Sigma A B s r t) -> Θ |> U.
Proof.
  move e:(Sigma A B s r t)=>n wr rs.
  elim: rs A B s r t wr e=>//{Θ m n}.
  move=>Θ Θ' l m m' fr rsm ihm A B s r t wr e; subst.
  destruct m; inv rsm.
  have->//:=free_wr_sigma fr wr.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Lemma resolve_pair_inv Θ m m1 m2 t :
  wr_env Θ -> resolve Θ m (Pair m1 m2 t) -> Θ |> t.
Proof.
  move e:(Pair m1 m2 t)=>n wr rs.
  elim: rs m1 m2 t e wr=>//{Θ m n}.
  move=>Θ1 Θ2 Θ m m' n n' t k mrg rsm ihm rsn ihn 
    m1 m2 t0 [_ _->] wr//.
  move=>Θ Θ' l m m' fr rsm ihm m1 m2 t e wr; subst.
  destruct m; inv rsm.
  destruct t.
  have->//:=free_wr_pair fr wr.
  apply: key_impure.
  exfalso. apply: free_wr_ptr; eauto.
Qed.

Theorem resolution Θ m n A t :
  nil ⊢ n : A : t -> value n -> wr_env Θ -> resolve Θ m n -> Θ |> t.
Proof with eauto using key_impure.
  move e:(nil)=>Γ ty. elim: ty Θ m e=>{Γ n A t}.
  move=>Γ s l k Θ m e val wr rs.
  { apply: resolve_sort_inv... }
  move=>Γ A B s r t i k tyA _ tyB _ Θ m _ val wr rs.
  { apply: resolve_pi_inv... }
  move=>Γ x A s hs Θ m _  val. inv val.
  move=>Γ A B m s r t i k tyP ihP tym ihm Θ n _ val wr rs.
  { destruct t...
    apply: resolve_lam_inv; eauto. }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym
    ihm tyn ihn Θ' m0 _ val. inv val.
  move=>Γ k Θ m _ val wr rs.
  { apply: resolve_unit_inv; eauto. }
  move=>Γ k Θ m _ v wr rs.
  { apply: resolve_it_inv; eauto. }
  move=>Γ A B s r t i lt k tyA ihA tyB ihB Θ m _ val wr rs.
  { apply: resolve_sigma_inv; eauto. }
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg tyS ihS 
    tym ihm tyn ihn Θ m0 _ val wr rs.
  { apply: resolve_pair_inv; eauto. }
  move=>Γ1 Γ2 Γ m n A s _ _ _ _ _ Θ m0 _ val. inv val.
  move=>Γ1 Γ2 Γ A B C m n s r t k x i 
    _ _ _ _ _ _ _ _ _ Θ m0 _ val. inv val.
  move=>Γ A B m s i sb tym ihm _ _ Θ m0 e val wr rs.
  { subst. apply: ihm... }
Qed.

Lemma wr_free_value Θ l m Θ' :
  free Θ l m Θ' -> wr_env Θ -> value m.
Proof with eauto using wr_env, value.
  elim=>{Θ l m Θ'}.
  move=>Θ m l e wr. inv wr...
  move=>Θ m l e wr. inv wr...
  move=>Θ m n A l fr ih wr.
  inv wr...
Qed.

Lemma resolve_value Θ m n :
  value m -> resolve Θ m n -> value n.
Proof with eauto using value.
  move=>v. elim: v Θ n=>{m}.
  move=>s l Θ n rs. inv rs...
  move=>A B s r t Θ n rs. inv rs...
  move=>A m s t Θ n rs. inv rs...
  move=>Θ n rs. inv rs...
  move=>Θ n rs. inv rs...
  move=>A B s r t Θ n rs. inv rs...
  move=>m n t Θ n0 rs. inv rs...
Qed.

Lemma wr_resolve_value Θ l n :
  wr_env Θ -> resolve Θ (Ptr l) n -> value n.
Proof.
  move=>wr rs. inv rs.
  have vm:=wr_free_value H0 wr.
  apply: resolve_value; eauto.
Qed.
