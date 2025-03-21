From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_dual clc_typing
  clc_weakening clc_substitution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma var_inv Γ x B s :
  Γ ⊢ Var x : B : s ->
  exists A t, has Γ x t A /\ A <: B /\ s = t.
Proof.
  move e:(Var x)=>m ty. elim: ty x e=>//{Γ m B s}.
  move=>Γ x A s hs x0 [e]; subst.
  exists A. exists s. eauto.
  move=>Γ A B m s i sb tym ihm tyB _ x e; subst.
  have[A0[t[hs[sb' e]]]]:=ihm _ erefl.
  exists A0. exists t.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma pi_inv Γ A B C s r t1 t2 :
  Γ ⊢ Pi A B s r t1 : C : t2 ->
  exists l,
    Γ ⊢ A : s @ l : U /\ t2 = U /\
    match s with U => A :U Γ | L => _: Γ end ⊢ B : r @ l : U.
Proof with eauto using key.
  move e:(Pi A B s r t1)=>m tp.
  elim: tp A B s r t1 e=>//{Γ C m t2}.
  move=>Γ A B s r t i k tyA ihA tyB ihB A0 B0 s0 r0 t1
    [e1 e2 e3 e4 e5]; subst.
  exists i.
  repeat split; eauto.
  destruct s.
  simpl in tyB. rewrite<-pure_re in tyB...
  simpl in tyB. rewrite<-pure_re in tyB...
Qed.

Lemma lam_invX Γ A1 A2 B C m s1 s2 r t1 t2 t3 l :
  Γ ⊢ Lam A1 m s1 t1 : C : t2 ->
  C <: Pi A2 B s2 r t3 ->
  [A2 :{s2} Γ] ⊢ B : r @ l : U ->
  A2 :{s2} Γ ⊢ m : B : r.
Proof.
  move e:(Lam A1 m s1 t1)=>n tpL.
  elim: tpL A1 A2 B m s1 s2 r t1 t3 l e=>//{Γ C n t2}.
  move=>Γ A B m s r t i k tyP ihP tym ihm A1 A2 B0 m0
    s1 s2 t2 t3 r0 l[e1 e2 e3 e4]/sub_pi_inv[c[sbB[e5[e6 e7]]]] tyB0; subst.
  { move:tyP=>/pi_inv[l0[tyA[_ tyB]]].
    destruct s2.
    apply: clc_conv; eauto.
    apply: context_conv.
    apply: conv_sym; eauto.
    eauto.
    eauto.
    apply: clc_conv; eauto.
    apply: context_conv.
    apply: conv_sym; eauto.
    eauto.
    eauto. }
  move=>Γ A B m s i sb1 tym ihm tyB ihB A1 A2 B0 m0 
    s1 t1 s2 t2 l e sb2 tyB0; subst.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma lam_inv Γ m A1 A2 B s1 s2 r t1 t2 t3 x l :
  [Γ] ⊢ Pi A1 B s1 r t1 : x @ l : U ->
  Γ ⊢ Lam A2 m s2 t2 : Pi A1 B s1 r t1 : t3 ->
  A1 :{s1} Γ ⊢ m : B : r.
Proof.
  move=> /pi_inv[i[tyA[_ tyB]]] tyL.
  apply: lam_invX; eauto.
Qed.

Lemma app_inv Γ m n C r :
  Γ ⊢ App m n : C : r ->
  exists Γ1 Γ2 A B s t,
    Γ2 |> s /\
    B.[n/] <: C /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : Pi A B s r t : t /\
    Γ2 ⊢ n : A : s.
Proof.
  move e:(App m n)=>x tp. elim: tp m n e=>//{Γ C r x}.
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym _ tyn _ m0 n0 [e1 e2]; subst.
  { exists Γ1. exists Γ2. exists A. exists B. exists s. exists t.
    repeat split; eauto. }
  move=>Γ A B m s i sb tym ihm tyB _ m0 n e; subst.
  { have[G1[G2[A0[B0[s0[t[k[sb'[mrg[tym0 tyn]]]]]]]]]]:=ihm _ _ erefl.
    exists G1. exists G2. exists A0. exists B0. exists s0. exists t.
    repeat split; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma unit_inv Γ A s : Γ ⊢ Unit : A : s -> exists i, U @ i <: A.
Proof.
  move e:(Unit)=>m tp. elim:tp e=>//{Γ A m s}.
  move=>Γ k _. exists 0; eauto.
  move=>Γ A B m s i sb tym ihm tyB ihB e; subst.
  have[l sb']:=ihm erefl.
  exists l. apply: sub_trans.
  exact: sb'. exact: sb.
Qed.

Lemma it_invX Γ1 A s :
  Γ1 ⊢ It : A : s -> A <: Unit -> Γ1 |> U.
Proof.
  move e:(It)=>m tp. elim:tp e=>//{Γ1 m A s}.
  move=>Γ A B m s i sb1 tym ihm tyB ihB e sb2; subst.
  apply: ihm; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma it_inv Γ1 s : Γ1 ⊢ It : Unit : s -> Γ1 |> U.
Proof. move=>ty. apply: it_invX; eauto. Qed.

Lemma left_inv Γ A s : Γ ⊢ Left : A : s -> Γ |> U.
Proof. move e:(Left)=>m tp. elim:tp e=>//{Γ m A s}. Qed.

Lemma right_inv Γ A s : Γ ⊢ Right : A : s -> Γ |> U.
Proof. move e:(Right)=>m tp. elim:tp e=>//{Γ m A s}. Qed.

Lemma sigma_invX Γ A B s r t C :
  Γ ⊢ Sigma A B s r t : C : U -> exists i, t @ i <: C.
Proof.
  move e:(Sigma A B s r t)=>m ty. 
  elim: ty A B s r t e=>//{Γ C m}.
  move=>Γ A B s r t i _ _ _ _ _ _ 
    A0 B0 s0 r0 t0[e1 e2 e3 e4 e5]; subst.
  exists i; eauto.
  move=>Γ A B m s i sb tym ihm tyB ihB A0 B0 s0 r t e; subst.
  have[l sb']:=ihm _ _ _ _ _ erefl.
  exists l. apply: sub_trans.
  exact: sb'. exact: sb.
Qed.

Lemma sigma_inv Γ A B s r t x :
  Γ ⊢ Sigma A B s r t : x : U ->
  exists Γ1 Γ2 i,
    s ⋅ r ≤ t /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ A : s @ i : U /\ 
    [A :{s} Γ2] ⊢ B : r @ i : U.
Proof.
  move e:(Sigma A B s r t)=>m ty. 
  elim: ty A B s r t e=>//{Γ x m}.
  move=>Γ A B s r t i mrg k 
    tyA ihA tyB ihB A0 B0 s0 r0 t0 [e1 e2 e3 e4 e5]; subst.
  exists Γ. exists Γ. 
  exists i. firstorder.
  by apply: merge_pure.
Qed.

Lemma pair_invX Γ m n t1 t3 C :
  Γ ⊢ Pair m n t1 : C : t3 ->
  forall A B s r t2 x l,
    C <: Sigma A B s r t2 ->
    [Γ] ⊢ Sigma A B s r t2 : x @ l : U ->
    exists Γ1 Γ2,
      t1 = t2 /\
      t2 = t3 /\
      Γ1 |> s /\ 
      Γ2 |> r /\
      Γ1 ∘ Γ2 => Γ /\
      Γ1 ⊢ m : A : s /\ 
      Γ2 ⊢ n : B.[m/] : r.
Proof.
  move e:(Pair m n t1)=>v tp. elim: tp m n t1 e=>//{Γ v C t3}.
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg.
  move=>/sigma_inv[G1[G2[i0[mrg0[tyA tyB]]]]].
  move=>_ tym _ tyn _ m0 n0 t1 [e1 e2 e3] A0 B0 s1 r1 t2 x l.
  move=>/sub_sigma_inv[sbA[sbB[e4[e5 e6]]]]; subst.
  move=>/sigma_inv[G3[G4[i1[_[mrg1[tyA0 tyB0]]]]]].
  { exists Γ1. exists Γ2.
    have[_[e1 e2]]:=merge_re_re mrg.
    have[_[e3 e4]]:=merge_re_re mrg1.
    rewrite<-re_invo in e3.
    rewrite<-re_invo in e4.
    have[k3 k4]:=merge_pure_inv mrg1 (re_pure _).
    repeat split; eauto.
    apply: clc_conv; eauto.
    rewrite e1.
    rewrite<-e3.
    rewrite<-pure_re; eauto.
    apply: clc_conv.
    apply: sub_subst; eauto.
    eauto.
    destruct s1; simpl in tyB0.
    { have mrg2:[G4] ∘ Γ1 => [Γ2].
      rewrite e4 e2 (pure_re k1) e1.
      apply: merge_re_id.
      have {}tym:Γ1 ⊢ m : A0 : U.
      apply:clc_conv; eauto.
      rewrite e1. rewrite<-e3. rewrite<-pure_re; eauto.
      have:=substitution tyB0 k1 mrg2 tym. 
      asimpl; eauto. }
    { have:=substitutionN tyB0 tym.
      rewrite e4. by rewrite<-e2. } }
  move=>Γ A B m s i sb1 tym ihm tyB ihB 
    m0 n e A0 B0 s0 r t x l sb2 tyS; subst.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma pair_inv Γ m n A B s r t1 t2 t3 x i :
  Γ ⊢ Pair m n t1 : Sigma A B s r t2 : t3 ->
  [Γ] ⊢ Sigma A B s r t2 : x @ i : U ->
  exists Γ1 Γ2,
    t1 = t2 /\
    t2 = t3 /\
    Γ1 |> s /\ 
    Γ2 |> r /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : A : s /\ 
    Γ2 ⊢ n : B.[m/] : r.
Proof. move=>tyP tyS. apply: pair_invX; eauto. Qed.

Lemma case_inv Γ m n1 n2 C s :
  Γ ⊢ Case m n1 n2 : C : s ->
  exists Γ1 Γ2 A,
    Γ1 ∘ Γ2 => Γ /\
    A.[m/] <: C /\
    Γ1 ⊢ m : Either : U /\
    Γ2 ⊢ n1 : A.[Left/] : s /\
    Γ2 ⊢ n2 : A.[Right/] : s.
Proof.
  move e:(Case m n1 n2)=>n tp. elim: tp m n1 n2 e=>//{Γ n C s}.
  move=>Γ1 Γ2 Γ m n1 n2 A s t i k mrg
    tym _ tyA _ tyn1 _ tyn2 _ m0 n0 n3 [e1 e2 e3]; subst.
  exists Γ1. exists Γ2. exists A.
  repeat split; eauto.
  move=>Γ A B m s i sb tym ihm _ _ m0 n1 n2 e; subst.
  have{ihm}[G1[G2[A0[mrg'[sb'[tym0[tyn1 tyn2]]]]]]]:=ihm _ _ _ erefl.
  exists G1. exists G2. exists A0.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma inp_inv Γ A B C s t :
  Γ ⊢ Inp A B s : C : t ->
  exists l,
    Γ ⊢ A : s @ l : U /\ t = U /\
    match s with U => A :U Γ | L => _: Γ end ⊢ B : Proto l : U.
Proof.
  move e:(Inp A B s)=>n tp. elim:tp A B s e=>//{Γ C t n}.
  move=>Γ A B s i k tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
  exists i.
  repeat split; eauto.
  destruct s; simpl in tyB.
  rewrite<-pure_re in tyB; eauto.
  rewrite<-pure_re in tyB; eauto.
Qed.

Lemma out_inv Γ A B C s t :
  Γ ⊢ Out A B s : C : t ->
  exists l,
    Γ ⊢ A : s @ l : U /\ t = U /\
    match s with U => A :U Γ | L => _: Γ end ⊢ B : Proto l : U.
Proof.
  move e:(Out A B s)=>n tp. elim:tp A B s e=>//{Γ C t n}.
  move=>Γ A B s i k tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
  exists i.
  repeat split; eauto.
  destruct s; simpl in tyB.
  rewrite<-pure_re in tyB; eauto.
  rewrite<-pure_re in tyB; eauto.
Qed.

Lemma ch_inv Γ A B s :
  Γ ⊢ Ch A : B : s ->
  exists i, Γ ⊢ A : Proto i : U.
Proof.
  move e:(Ch A)=>n tp. elim: tp A e=>//{Γ B s n}.
  move=>Γ A i k tyA ihA A0 [e]; subst.
  by exists i.
Qed.

Lemma fork_inv Γ m n T r :
  Γ ⊢ Fork m n : T : r ->
  exists Γ1 Γ2 A B C s t i,
    r = L /\
    Sigma (Ch A) Main L L L <: T /\
    A ~ B /\
    Γ1 ∘ Γ2 => Γ /\
    [Γ1] ⊢ Ch A : L @ i : U /\
    [Γ2] ⊢ Ch B : L @ i : U /\
    Γ1 ⊢ m : Main : L /\
    Γ2 ⊢ n : Pi (Ch B) C L s t : t.
Proof.
  move e:(Fork m n)=>x tp. elim: tp m n e=>//{Γ x T r}.
  move=>Γ1 Γ2 Γ m n A B C s t i d mrg tyA _ tyB _ tym _ tyn _ m0 n0 [e1 e2]; subst.
  exists Γ1. exists Γ2. exists A. exists B. exists C. exists s. exists t. exists i.
  repeat split; eauto.
  move=>Γ A B m s i sb tym ih tyB _ m0 n e; subst.
  have{ih}[G1[G2[Ax[Bx[Cx[s0[t0[i0 e]]]]]]]]:=ih _ _ erefl.
  firstorder; subst.
  exists G1. exists G2. exists Ax. exists Bx. exists Cx. exists s0. exists t0. exists i0.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma recv_inv Γ m C t :
  Γ ⊢ Recv m : C : t ->
  exists A B s,
    t = L /\
    Sigma A (Ch B) s L L <: C /\
    Γ ⊢ m : Ch (Inp A B s) : L.
Proof.
  move e:(Recv m)=>n tp. elim: tp m e=>//{Γ C t n}.
  move=>Γ A B m s tym _ m0 [e]; subst.
  exists A. exists B. by exists s.
  move=>Γ A B m s i sb tym ih tyB _ m0 e; subst.
  have[A0[B0[s0[e[sb0 tym0]]]]]:=ih _ erefl; subst.
  exists A0. exists B0. exists s0.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma send_inv Γ m C t :
  Γ ⊢ Send m : C : t ->
  exists A B s,
    t = L /\
    Pi A (Ch B) s L L <: C /\
    Γ ⊢ m : Ch (Out A B s) : L.
Proof.
  move e:(Send m)=>n tp. elim: tp m e=>//{Γ C t n}.
  move=>Γ A B m s tym _ m0 [e]; subst.
  exists A. exists B. by exists s.
  move=>Γ A B m s i sb tym ih tyB _ m0 e; subst.
  have[A0[B0[s0[e[sb0 tym0]]]]]:=ih _ erefl.
  exists A0. exists B0. exists s0.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma close_inv Γ m A s :
  Γ ⊢ Close m : A : s ->
  s = U /\
  Unit <: A /\
  Γ ⊢ m : Ch OutEnd : L.
Proof.
  move e:(Close m)=>n tp. elim: tp m e=>//{Γ A s n}.
  move=>Γ m tym ihm m0 [e]; subst=>//.
  move=>Γ A B m s i sb tym ihm tyB _ m0 [e]; subst.
  have[->[sb' tym0]]:=ihm _ erefl.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma wait_inv Γ m A s :
  Γ ⊢ Wait m : A : s ->
  s = U /\
  Unit <: A /\
  Γ ⊢ m : Ch InpEnd : L.
Proof.
  move e:(Wait m)=>n tp. elim: tp m e=>//{Γ A s n}.
  move=>Γ m tym ihm m0 [e]; subst=>//.
  move=>Γ A B m s i sb tym ihm tyB _ m0 [e]; subst.
  have[->[sb' tym0]]:=ihm _ erefl.
  repeat split; eauto.
  apply: sub_trans; eauto.
Qed.

