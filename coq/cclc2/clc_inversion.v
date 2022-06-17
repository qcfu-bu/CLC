From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_typing
  clc_weakening clc_substitution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma var_inv Γ x B s :
  Γ ⊢ Var x : B : s ->
  exists A t, has Γ x t A /\ A === B /\ s = t.
Proof.
  move e:(Var x)=>m ty. elim: ty x e=>//{Γ m B s}.
  move=>Γ x A s hs x0 [e]; subst.
  exists A. exists s. eauto.
  move=>Γ A B m s sb tym ihm tyB _ x e; subst.
  have[A0[t[hs[sb' e]]]]:=ihm _ erefl.
  exists A0. exists t.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma pi_inv Γ A B C s r t1 t2 :
  Γ ⊢ Pi A B s r t1 : C : t2 ->
  Γ ⊢ A : Sort s : U /\ t2 = U /\
  match s with U => A :U Γ | L => _: Γ end ⊢ B : Sort r : U.
Proof with eauto using key.
  move e:(Pi A B s r t1)=>m tp.
  elim: tp A B s r t1 e=>//{Γ C m t2}.
  move=>Γ A B s r t k tyA ihA tyB ihB A0 B0 s0 r0 t1
    [e1 e2 e3 e4 e5]; subst.
  repeat split; eauto.
  destruct s.
  simpl in tyB. rewrite<-pure_re in tyB...
  simpl in tyB. rewrite<-pure_re in tyB...
Qed.

Lemma lam_invX Γ A1 A2 B C m s1 s2 r t1 t2 t3 :
  Γ ⊢ Lam A1 m s1 t1 : C : t2 ->
  C === Pi A2 B s2 r t3 ->
  [A2 :{s2} Γ] ⊢ B : Sort r : U ->
  A2 :{s2} Γ ⊢ m : B : r.
Proof.
  move e:(Lam A1 m s1 t1)=>n tpL.
  elim: tpL A1 A2 B m s1 s2 r t1 t3 e=>//{Γ C n t2}.
  move=>Γ A B m s r t k tyP ihP tym ihm A1 A2 B0 m0
    s1 s2 t2 t3 r0[e1 e2 e3 e4]/pi_inj[cA[cB[e5[e6 e7]]]]tyB0; subst.
  { move:tyP=>/pi_inv[tyA[_ tyB]].
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
    s1 t1 r s2 t2 e c tyB0; subst.
  { apply: ihm; eauto.
    apply: conv_trans; eauto. }
Qed.

Lemma lam_inv Γ m A1 A2 B s1 s2 r t1 t2 t3 x :
  [Γ] ⊢ Pi A1 B s1 r t1 : Sort x : U ->
  Γ ⊢ Lam A2 m s2 t2 : Pi A1 B s1 r t1 : t3 ->
  A1 :{s1} Γ ⊢ m : B : r.
Proof.
  move=> /pi_inv[tyA[_ tyB]] tyL.
  apply: lam_invX; eauto.
Qed.

Lemma app_inv Γ m n C r :
  Γ ⊢ App m n : C : r ->
  exists Γ1 Γ2 A B s t,
    Γ2 |> s /\
    B.[n/] === C /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : Pi A B s r t : t /\
    Γ2 ⊢ n : A : s.
Proof.
  move e:(App m n)=>x tp. elim: tp m n e=>//{Γ C r x}.
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym _ tyn _ m0 n0 [e1 e2]; subst.
  { exists Γ1. exists Γ2. exists A. exists B. exists s. exists t.
    repeat split; eauto. }
  move=>Γ A B m s sb tym ihm tyB _ m0 n e; subst.
  { have[G1[G2[A0[B0[s0[t[k[sb'[mrg[tym0 tyn]]]]]]]]]]:=ihm _ _ erefl.
    exists G1. exists G2. exists A0. exists B0. exists s0. exists t.
    repeat split; eauto.
    apply: conv_trans; eauto. }
Qed.

Lemma unit_inv Γ A s : Γ ⊢ Unit : A : s -> Sort U === A.
Proof.
  move e:(Unit)=>m tp. elim:tp e=>//{Γ A m s}.
  move=>Γ A B m s sb tym ihm tyB ihB e; subst.
  have sb':=ihm erefl.
  apply: conv_trans.
  exact: sb'. exact: sb.
Qed.

Lemma it_invX Γ1 A s :
  Γ1 ⊢ It : A : s -> A === Unit -> Γ1 |> U.
Proof.
  move e:(It)=>m tp. elim:tp e=>//{Γ1 m A s}.
  move=>Γ A B m s sb1 tym ihm tyB ihB e sb2; subst.
  apply: ihm; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma it_inv Γ1 s : Γ1 ⊢ It : Unit : s -> Γ1 |> U.
Proof. move=>ty. apply: it_invX; eauto. Qed.

Lemma left_inv Γ A s : Γ ⊢ Left : A : s -> Γ |> U.
Proof. move e:(Left)=>m tp. elim:tp e=>//{Γ m A s}. Qed.

Lemma right_inv Γ A s : Γ ⊢ Right : A : s -> Γ |> U.
Proof. move e:(Right)=>m tp. elim:tp e=>//{Γ m A s}. Qed.

Lemma sigma_invX Γ A B s r t C :
  Γ ⊢ Sigma A B s r t : C : U -> Sort t === C.
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
  Γ ⊢ Sigma A B s r t : x : U ->
  exists Γ1 Γ2,
    s ⋅ r ≤ t /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ A : Sort s : U /\
    [A :{s} Γ2] ⊢ B : Sort r : U.
Proof.
  move e:(Sigma A B s r t)=>m ty. 
  elim: ty A B s r t e=>//{Γ x m}.
  move=>Γ A B s r t mrg k
    tyA ihA tyB ihB A0 B0 s0 r0 t0 [e1 e2 e3 e4 e5]; subst.
  exists Γ. exists Γ. firstorder.
  by apply: merge_pure.
Qed.

Lemma pair_invX Γ m n t1 t3 C :
  Γ ⊢ Pair m n t1 : C : t3 ->
  forall A B s r t2 x,
    C === Sigma A B s r t2 ->
    [Γ] ⊢ Sigma A B s r t2 : Sort x : U ->
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
      have {}tym:Γ1 ⊢ m : A0 : U.
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

Lemma pair_inv Γ m n A B s r t1 t2 t3 x :
  Γ ⊢ Pair m n t1 : Sigma A B s r t2 : t3 ->
  [Γ] ⊢ Sigma A B s r t2 : Sort x : U ->
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
    A.[m/] === C /\
    Γ1 ⊢ m : Either : U /\
    Γ2 ⊢ n1 : A.[Left/] : s /\
    Γ2 ⊢ n2 : A.[Right/] : s.
Proof.
  move e:(Case m n1 n2)=>n tp. elim: tp m n1 n2 e=>//{Γ n C s}.
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

Lemma act_inv Γ r A B C s t :
  Γ ⊢ Act r A B s : C : t ->
  Γ ⊢ A : Sort s : U /\ t = U /\
  match s with U => A :U Γ | L => _: Γ end ⊢ B : Proto : U.
Proof.
  move e:(Act r A B s)=>n tp. elim:tp r A B s e=>//{Γ C t n}.
  move=>Γ r A B s k tyA ihA tyB ihB r0 A0 B0 s0 [e1 e2 e3 e4]; subst.
  repeat split; eauto.
  destruct s; simpl in tyB.
  rewrite<-pure_re in tyB; eauto.
  rewrite<-pure_re in tyB; eauto.
Qed.

Lemma ch_inv Γ r A B s :
  Γ ⊢ Ch r A : B : s ->
  Γ ⊢ A : Proto : U.
Proof.
  move e:(Ch r A)=>n tp. elim: tp r A e=>//{Γ B s n}.
  move=>Γ r A k tyA ihA r0 A0 [e1 e2]; subst=>//.
Qed.

Lemma fork_inv Γ m n T r :
  Γ ⊢ Fork m n : T : r ->
  exists Γ1 Γ2 r1 r2 A B s t,
    r = L /\
    Sigma (Ch r1 A) Main L L L === T /\
    Γ1 ∘ Γ2 => Γ /\
    r1 = ~~ r2 /\
    [Γ] ⊢ A : Proto : U /\
    Γ1 ⊢ m : Main : L /\
    Γ2 ⊢ n : Pi (Ch r2 A) B L s t : t.
Proof.
  move e:(Fork m n)=>x tp. elim: tp m n e=>//{Γ x T r}.
  move=>Γ1 Γ2 r1 r2 Γ m n A B s t mrg d tyA _ tym _ tyn _ m0 n0 [e1 e2]; subst.
  exists Γ1. exists Γ2. exists (~~r2). exists r2. exists A. exists B. exists s. exists t.
  repeat split; eauto.
  move=>Γ A B m s sb tym ih tyB _ m0 n e; subst.
  have{ih}[G1[G2[r1[r2[A0[B0[s0[t0]]]]]]]]:=ih _ _ erefl.
  firstorder; subst.
  exists G1. exists G2. exists (~~r2). exists r2. exists A0. exists B0. exists s0. exists t0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma recv_inv Γ m C t :
  Γ ⊢ Recv m : C : t ->
  exists r1 r2 A B s,
    t = L /\
    Sigma A (Ch r1 B) s L L === C /\
    addb r1 r2 = false /\
    Γ ⊢ m : Ch r1 (Act r2 A B s) : L.
Proof.
  move e:(Recv m)=>n tp. elim: tp m e=>//{Γ C t n}.
  move=>Γ r1 r2 A B m s xor tym _ m0 [e]; subst.
  exists r1. exists r2. exists A. exists B. by exists s.
  move=>Γ A B m s sb tym ih tyB _ m0 e; subst.
  have[r1[r2[A0[B0[s0]]]]]:=ih _ erefl.
  firstorder; subst.
  exists r1. exists r2. exists A0. exists B0. exists s0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma send_inv Γ m C t :
  Γ ⊢ Send m : C : t ->
  exists r1 r2 A B s,
    t = L /\
    Pi A (Ch r1 B) s L L === C /\
    addb r1 r2 = true /\
    Γ ⊢ m : Ch r1 (Act r2 A B s) : L.
Proof.
  move e:(Send m)=>n tp. elim: tp m e=>//{Γ C t n}.
  move=>Γ r1 r2 A B m s xor tym _ m0 [e]; subst.
  exists r1. exists r2. exists A. exists B. by exists s.
  move=>Γ A B m s sb tym ih tyB _ m0 e; subst.
  have[r1[r2[A0[B0[s0]]]]]:=ih _ erefl.
  firstorder; subst.
  exists r1. exists r2. exists A0. exists B0. exists s0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma wait_inv Γ m A s :
  Γ ⊢ Wait m : A : s ->
  exists r1 r2,
    s = U /\
    Unit === A /\
    addb r1 r2 = false /\
    Γ ⊢ m : Ch r1 (Stop r2) : L.
Proof.
  move e:(Wait m)=>n tp. elim: tp m e=>//{Γ A s n}.
  move=>Γ r1 r2 m xor tym ihm m0 [e]; subst=>//.
  exists r1. exists r2. eauto.
  move=>Γ A B m s sb tym ihm tyB _ m0 [e]; subst.
  have[r1[r2[->[sb0[xor tym0]]]]]:=ihm _ erefl.
  exists r1. exists r2.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma close_inv Γ m A s :
  Γ ⊢ Close m : A : s ->
  exists r1 r2,
    s = U /\
    Unit === A /\
    addb r1 r2 = true /\
    Γ ⊢ m : Ch r1 (Stop r2) : L.
Proof.
  move e:(Close m)=>n tp. elim: tp m e=>//{Γ A s n}.
  move=>Γ r1 r2 m xor tym ihm m0 [e]; subst=>//.
  exists r1. exists r2. eauto.
  move=>Γ A B m s sb tym ihm tyB _ m0 [e]; subst.
  have[r1[r2[->[sb0[xor tym0]]]]]:=ihm _ erefl.
  exists r1. exists r2.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.
