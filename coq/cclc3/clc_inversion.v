From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Export clc_substitution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma var_inv Γ x B :
  Γ ⊢ Var x : B -> exists A t, has Γ x t A /\ A === B.
Proof.
  move e:(Var x)=>m ty. elim: ty x e=>//{Γ m B}.
  move=>Γ x A s hs x0 [e]; subst.
  exists A. exists s. eauto.
  move=>Γ A B m s sb tym ihm tyB _ x e; subst.
  have[A0[t[hs e]]]:=ihm _ erefl.
  exists A0. exists t.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma pi_inv Γ A B C s t :
  Γ ⊢ Pi A B s t : C ->
  Γ ⊢ A : Sort s /\
  exists r, [A :{s} Γ] ⊢ B : Sort r.
Proof with eauto using key.
  move e:(Pi A B s t)=>m tp.
  elim: tp A B s t e=>//{Γ C m}.
  move=>Γ A B s r t k tyA ihA tyB ihB A0 B0 s0 r0
    [e1 e2 e3 e4]; subst.
  repeat split; eauto.
Qed.

Lemma lam_invX Γ A1 A2 B C m s1 s2 r t1 t2 :
  Γ ⊢ Lam A1 m s1 t1 : C ->
  C === Pi A2 B s2 t2 ->
  [A2 :{s2} Γ] ⊢ B : Sort r ->
  A2 :{s2} Γ ⊢ m : B.
Proof.
  move e:(Lam A1 m s1 t1)=>n tpL.
  elim: tpL A1 A2 B m s1 s2 r t1 t2 e=>//{Γ C n}.
  move=>Γ A B m s t k tyP ihP tym ihm A1 A2 B0 m0
    s1 s2 r1 t1 t2[e1 e2 e3 e4]/pi_inj[cA[cB[e5 e6]]]tyB0; subst.
  { move:tyP=>/pi_inv[tyA[r2 tyB]].
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
  move=>Γ A B m s sb1 tym ihm tyB ihB A1 A2 B0 m0
    s1 s2 r t1 t2 e c tyB0; subst.
  { apply: ihm; eauto.
    apply: conv_trans; eauto. }
Qed.

Lemma lam_inv Γ m A1 A2 B s1 s2 t1 t2 x :
  [Γ] ⊢ Pi A1 B s1 t1 : Sort x ->
  Γ ⊢ Lam A2 m s2 t2 : Pi A1 B s1 t1 ->
  A1 :{s1} Γ ⊢ m : B.
Proof.
  move=>/pi_inv[tyA[r tyB]] tyL.
  apply: lam_invX; eauto.
  simpl.
  simpl in tyB.
  rewrite<-re_invo in tyB.
  eauto.
Qed.

Lemma app_inv Γ m n C :
  Γ ⊢ App m n : C ->
  exists Γ1 Γ2 A B s t,
    Γ2 |> s /\
    B.[n/] === C /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : Pi A B s t /\
    Γ2 ⊢ n : A.
Proof.
  move e:(App m n)=>x tp. elim: tp m n e=>//{Γ C x}.
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym _ tyn _ m0 n0 [e1 e2]; subst.
  { exists Γ1. exists Γ2. exists A. exists B. exists s. exists t.
    repeat split; eauto. }
  move=>Γ A B m s sb tym ihm tyB _ m0 n e; subst.
  { have[G1[G2[A0[B0[s0[t[k[sb'[mrg[tym0 tyn]]]]]]]]]]:=ihm _ _ erefl.
    exists G1. exists G2. exists A0. exists B0. exists s0. exists t.
    repeat split; eauto.
    apply: conv_trans; eauto. }
Qed.

Lemma unit_inv Γ A : Γ ⊢ Unit : A -> Sort U === A.
Proof.
  move e:(Unit)=>m tp. elim:tp e=>//{Γ A m}.
  move=>Γ A B m s sb tym ihm tyB ihB e; subst.
  have sb':=ihm erefl.
  apply: conv_trans.
  exact: sb'. exact: sb.
Qed.

Lemma it_invX Γ1 A :
  Γ1 ⊢ It : A -> A === Unit -> Γ1 |> U.
Proof.
  move e:(It)=>m tp. elim:tp e=>//{Γ1 m A}.
  move=>Γ A B m s sb1 tym ihm tyB ihB e sb2; subst.
  apply: ihm; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma it_inv Γ1 : Γ1 ⊢ It : Unit -> Γ1 |> U.
Proof. move=>ty. apply: it_invX; eauto. Qed.

Lemma left_inv Γ A : Γ ⊢ Left : A -> Γ |> U.
Proof. move e:(Left)=>m tp. elim:tp e=>//{Γ m A}. Qed.

Lemma right_inv Γ A : Γ ⊢ Right : A -> Γ |> U.
Proof. move e:(Right)=>m tp. elim:tp e=>//{Γ m A}. Qed.

Lemma sigma_invX Γ A B s r t C :
  Γ ⊢ Sigma A B s r t : C -> Sort t === C.
Proof.
  move e:(Sigma A B s r t)=>m ty. 
  elim: ty A B s r t e=>//{Γ C m}.
  move=>Γ A B s r t _ _ _ _ _ _
    A0 B0 s0 r0 t0[e1 e2 e3 e4 e5]; subst.
  eauto.
  move=>Γ A B m s sb tym ihm tyB ihB A0 B0 s0 r t e; subst.
  have sb':=ihm _ _ _ _ _ erefl.
  apply: conv_trans.
  exact: sb'. exact: sb.
Qed.

Lemma sigma_inv Γ A B s r t x :
  Γ ⊢ Sigma A B s r t : x ->
  exists Γ1 Γ2,
    s ⋅ r ≤ t /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ A : Sort s /\
    [A :{s} Γ2] ⊢ B : Sort r.
Proof.
  move e:(Sigma A B s r t)=>m ty. 
  elim: ty A B s r t e=>//{Γ x m}.
  move=>Γ A B s r t mrg k
    tyA ihA tyB ihB A0 B0 s0 r0 t0 [e1 e2 e3 e4 e5]; subst.
  exists Γ. exists Γ. firstorder.
  by apply: merge_pure.
Qed.

Lemma pair_invX Γ m n t1 C :
  Γ ⊢ Pair m n t1 : C ->
  forall A B s r t2 x,
    C === Sigma A B s r t2 ->
    [Γ] ⊢ Sigma A B s r t2 : Sort x ->
    exists Γ1 Γ2,
      t1 = t2 /\
      Γ1 |> s /\ 
      Γ2 |> r /\
      Γ1 ∘ Γ2 => Γ /\
      Γ1 ⊢ m : A /\ 
      Γ2 ⊢ n : B.[m/].
Proof.
  move e:(Pair m n t1)=>v tp. elim: tp m n t1 e=>//{Γ v C}.
  move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg.
  move=>/sigma_inv[G1[G2[mrg0[tyA tyB]]]].
  move=>_ tym _ tyn _ m0 n0 t1 [e1 e2 e3] A0 B0 s1 r1 t2 x.
  move=>/sigma_inj[sbA[sbB[e4[e5 e6]]]]; subst.
  move=>/sigma_inv[G3[G4[_[mrg1[tyA0 tyB0]]]]].
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
    apply: conv_subst; eauto.
    eauto.
    destruct s1; simpl in tyB0.
    { have mrg2:[G4] ∘ Γ1 => [Γ2].
      rewrite e4 e2 (pure_re k1) e1.
      apply: merge_re_id.
      have {}tym:Γ1 ⊢ m : A0.
      apply:clc_conv; eauto.
      rewrite e1. rewrite<-e3. rewrite<-pure_re; eauto.
      have:=substitution tyB0 k1 mrg2 tym. 
      asimpl; eauto. }
    { have:=substitutionN tyB0 tym.
      rewrite e4. by rewrite<-e2. } }
  move=>Γ A B m s sb1 tym ihm tyB ihB
    m0 n e A0 B0 s0 r t x sb2 tyS; subst.
  { apply: ihm; eauto.
    apply: conv_trans; eauto. }
Qed.

Lemma pair_inv Γ m n A B s r t1 t2 x :
  Γ ⊢ Pair m n t1 : Sigma A B s r t2 ->
  [Γ] ⊢ Sigma A B s r t2 : Sort x ->
  exists Γ1 Γ2,
    t1 = t2 /\
    Γ1 |> s /\ 
    Γ2 |> r /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : A /\ 
    Γ2 ⊢ n : B.[m/].
Proof. move=>tyP tyS. apply: pair_invX; eauto. Qed.

Lemma case_inv Γ m n1 n2 C :
  Γ ⊢ Case m n1 n2 : C ->
  exists Γ1 Γ2 A,
    Γ1 ∘ Γ2 => Γ /\
    A.[m/] === C /\
    Γ1 ⊢ m : Either /\
    Γ2 ⊢ n1 : A.[Left/] /\
    Γ2 ⊢ n2 : A.[Right/].
Proof.
  move e:(Case m n1 n2)=>n tp. elim: tp m n1 n2 e=>//{Γ n C}.
  move=>Γ1 Γ2 Γ m n1 n2 A s t k mrg
    tym _ tyA _ tyn1 _ tyn2 _ m0 n0 n3 [e1 e2 e3]; subst.
  exists Γ1. exists Γ2. exists A.
  repeat split; eauto.
  move=>Γ A B m s sb tym ihm _ _ m0 n1 n2 e; subst.
  have{ihm}[G1[G2[A0[mrg'[sb'[tym0[tyn1 tyn2]]]]]]]:=ihm _ _ _ erefl.
  exists G1. exists G2. exists A0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma act_inv Γ r A B C s :
  Γ ⊢ Act r A B s : C ->
  Γ ⊢ A : Sort s /\
  [A :{s} Γ] ⊢ B : Proto.
Proof.
  move e:(Act r A B s)=>n tp. elim:tp r A B s e=>//{Γ C n}.
  move=>Γ r A B s k tyA ihA tyB ihB r0 A0 B0 s0 [e1 e2 e3 e4]; subst.
  repeat split; eauto.
Qed.

Lemma ch_inv Γ r A B :
  Γ ⊢ Ch r A : B -> Γ ⊢ A : Proto.
Proof.
  move e:(Ch r A)=>n tp. elim: tp r A e=>//{Γ B n}.
  move=>Γ r A k tyA ihA r0 A0 [e1 e2]; subst=>//.
Qed.

Lemma fork_inv Γ m n T :
  Γ ⊢ Fork m n : T ->
  exists Γ1 Γ2 r1 r2 A B t,
    Sigma (Ch r1 A) Main L L L === T /\
    Γ1 ∘ Γ2 => Γ /\
    r1 = ~~ r2 /\
    [Γ] ⊢ A : Proto /\
    Γ1 ⊢ m : Main /\
    Γ2 ⊢ n : Pi (Ch r2 A) B L t.
Proof.
  move e:(Fork m n)=>x tp. elim: tp m n e=>//{Γ x T}.
  move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tyA _ tym _ tyn _ m0 n0 [e1 e2]; subst.
  exists Γ1. exists Γ2. exists (~~r2). exists r2. exists A. exists B. exists t.
  repeat split; eauto.
  move=>Γ A B m s sb tym ih tyB _ m0 n e; subst.
  have[G1[G2[r1[r2[A0[B0[t0]]]]]]]:=ih _ _ erefl.
  firstorder; subst.
  exists G1. exists G2. exists (~~r2). exists r2. exists A0. exists B0. exists t0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma recv_inv Γ m C :
  Γ ⊢ Recv m : C ->
  exists r1 r2 A B s,
    Sigma A (Ch r1 B) s L L === C /\
    addb r1 r2 = false /\
    Γ ⊢ m : Ch r1 (Act r2 A B s).
Proof.
  move e:(Recv m)=>n tp. elim: tp m e=>//{Γ C n}.
  move=>Γ r1 r2 A B m s xor tym _ m0 [e]; subst.
  exists r1. exists r2. exists A. exists B. by exists s.
  move=>Γ A B m s sb tym ih tyB _ m0 e; subst.
  have[r1[r2[A0[B0[s0]]]]]:=ih _ erefl.
  firstorder; subst.
  exists r1. exists r2. exists A0. exists B0. exists s0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma send_inv Γ m C :
  Γ ⊢ Send m : C ->
  exists r1 r2 A B s,
    Pi A (Ch r1 B) s L === C /\
    addb r1 r2 = true /\
    Γ ⊢ m : Ch r1 (Act r2 A B s).
Proof.
  move e:(Send m)=>n tp. elim: tp m e=>//{Γ C n}.
  move=>Γ r1 r2 A B m s xor tym _ m0 [e]; subst.
  exists r1. exists r2. exists A. exists B. by exists s.
  move=>Γ A B m s sb tym ih tyB _ m0 e; subst.
  have[r1[r2[A0[B0[s0]]]]]:=ih _ erefl.
  firstorder; subst.
  exists r1. exists r2. exists A0. exists B0. exists s0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma wait_inv Γ m A :
  Γ ⊢ Wait m : A ->
  exists r1 r2,
    Unit === A /\
    addb r1 r2 = false /\
    Γ ⊢ m : Ch r1 (Stop r2).
Proof.
  move e:(Wait m)=>n tp. elim: tp m e=>//{Γ A n}.
  move=>Γ r1 r2 m xor tym ihm m0 [e]; subst=>//.
  exists r1. exists r2. eauto.
  move=>Γ A B m s sb tym ihm tyB _ m0 [e]; subst.
  have[r1[r2[sb0[xor tym0]]]]:=ihm _ erefl.
  exists r1. exists r2.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma close_inv Γ m A :
  Γ ⊢ Close m : A ->
  exists r1 r2,
    Unit === A /\
    addb r1 r2 = true /\
    Γ ⊢ m : Ch r1 (Stop r2).
Proof.
  move e:(Close m)=>n tp. elim: tp m e=>//{Γ A n}.
  move=>Γ r1 r2 m xor tym ihm m0 [e]; subst=>//.
  exists r1. exists r2. eauto.
  move=>Γ A B m s sb tym ihm tyB _ m0 [e]; subst.
  have[r1[r2[sb0[xor tym0]]]]:=ihm _ erefl.
  exists r1. exists r2.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.
