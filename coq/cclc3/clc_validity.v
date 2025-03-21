From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Export clc_inversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma merge_context_ok_inv Γ Γ1 Γ2 :
  Γ1 ∘ Γ2 => Γ -> ok Γ -> ok Γ1 /\ ok Γ2.
Proof with eauto using ok.
  elim=>{Γ1 Γ2 Γ}...
  move=>Γ1 Γ2 Γ m mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H1)=>{ih H1}[o1 o2].
    split.
    apply: ty_ok...
    rewrite e1...
    apply: ty_ok...
    rewrite e2... }
  move=>Γ1 Γ2 Γ m mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H1)=>{ih H1}[o1 o2].
    split.
    apply: ty_ok...
    rewrite e1...
    apply: n_ok... }
  move=>Γ1 Γ2 Γ m mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H1)=>{ih H1}[o1 o2].
    split.
    apply: n_ok...
    apply: ty_ok...
    rewrite e2... }
  move=>Γ1 Γ2 Γ mrg ih o. inv o.
  { move:(merge_re_re mrg)=>[_[e1 e2]].
    move:(ih H0)=>{ih H0}[o1 o2].
    split... }
Qed.

Theorem validity Γ m A :
  ok Γ -> Γ ⊢ m : A -> exists s, [Γ] ⊢ A : Sort s.
Proof with eauto using clc_type, re_pure, merge_re_id, key.
  move=>wf tp. elim: tp wf=>{Γ m A}.
  move=>Γ s k o...
  move=>Γ A B s r t k tyA ihA tyB ihB o...
  move=>Γ x A s hs o. move:(has_ok o hs)=>tyA...
  move=>Γ A B m s t k tyP ihP tym ihm o...
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn o.
    move:(merge_context_ok_inv mrg o)=>[o1 o2].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    move:o1=>/ihm{ihm}[_/pi_inv[tyA[r tyB]]].
    destruct s.
    have {}mrg : [Γ1] ∘ Γ2 => [Γ].
      replace Γ2 with [Γ2].
      rewrite e2 e3...
      rewrite<-pure_re...
    simpl in tyB. rewrite<-re_invo in tyB.
    exists r. by apply: (substitution tyB k mrg tyn).
    simpl in tyB. rewrite<-re_invo in tyB.
    exists r. have:=substitutionN n tyB.
    by rewrite e2.
  move=>Γ A m k tyA ihA tym ihm o.
    rewrite<-pure_re...
  move=>Γ k o...
  move=>Γ k o...
  move=>Γ k o...
  move=>Γ k o...
  move=>Γ k o...
  move=>Γ A B s r t leq k tyA ihA tyB ihB o...
  move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg
    tyS ihS tym ihm tyn ihn o...
  move=>Γ1 Γ2 Γ m n1 n2 A s t k mrg tym _ tyA ihA _ _ _ _ wf.
    have[_[e1 e2]]:=merge_re_re mrg.
    destruct s; simpl in tyA.
    have{}mrg:[Γ2] ∘ Γ1 => [Γ].
    { replace Γ1 with [Γ1].
      apply: merge_re3. apply: merge_sym...
      rewrite<-pure_re... }
    exists t. have//:=substitution tyA k mrg tym.
    exists t. have:=substitutionN m tyA.
    by rewrite e2.
  move=>Γ1 Γ2 Γ m n A s t k mrg tym ihm tyA ihA tyn ihn o.
    move:(merge_re_re mrg)=>[e0[e1 e2]].
    destruct s; simpl in tyA.
    have mrg1:[Γ2] ∘ Γ1 => [Γ].
    rewrite e2 (pure_re k) e1.
    apply: merge_re_id.
    exists t. have:=substitution tyA k mrg1 tym. by asimpl.
    exists t. have:=substitutionN m tyA. rewrite e2. by asimpl.
  move=>Γ1 Γ2 Γ A B C m n s r t k x leq key mrg
    tym _ tyC _ tyn _ o.
    move:(merge_re_re mrg)=>[e0[e1 e2]].
    destruct k; simpl in tyC.
    have mrg1:[Γ2] ∘ Γ1 => [Γ].
    rewrite e2 (pure_re key) e1.
    apply: merge_re_id. inv leq.
    exists x. have:=substitution tyC key mrg1 tym.
    by asimpl.
    exists x. have:=substitutionN m tyC.
    by rewrite e2.
  move=>Γ k wf...
  move=>Γ k o...
  move=>Γ r k o...
  move=>Γ r A B s k tyA ihA tyB ihB o...
  move=>Γ r A k tyA ihA o...
  move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tym ihm tyn ihn wf.
    have[wf1 wf2]:=merge_context_ok_inv mrg wf.
    have[_[e1 e2]]:=merge_re_re mrg.
    have[s/pi_inv[/ch_inv tyA _]]:=ihn wf2.
    exists L. econstructor; simpl...
    constructor.
    constructor...
    rewrite<-e2...
  move=>Γ r1 r2 A B m s xor tym ihm o.
    have[r/ch_inv/act_inv[tyA tyB]]:=ihm o.
    exists L. apply: clc_sigma...
    destruct s; simpl; constructor.
  move=>Γ r1 r2 A B m s xor tym ihm o.
    have[r/ch_inv/act_inv[tyA tyB]]:=ihm o.
    exists L. apply: clc_pi...
  move=>Γ r1 r2 m xor tym ihm o...
  move=>Γ r1 r2 m xor tym ihm o...
  move=>Γ A B m s sb tym ihm tyB ihB o...
Qed.

Lemma fork_inv Γ m n T :
  ok Γ -> Γ ⊢ Fork m n : T ->
  exists Γ1 Γ2 r1 r2 A B t,
    Sigma (Ch r1 A) Main L L L === T /\
    Γ1 ∘ Γ2 => Γ /\
    r1 = ~~ r2 /\
    [Γ] ⊢ A : Proto /\
    Γ1 ⊢ m : Main /\
    Γ2 ⊢ n : Pi (Ch r2 A) B L t.
Proof.
  move e:(Fork m n)=>x wf tp. elim: tp wf m n e=>//{Γ x T}.
  move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tym _ tyn _ wf m0 n0 [e1 e2]; subst.
  exists Γ1. exists Γ2. exists (~~r2). exists r2. exists A. exists B. exists t.
  repeat split; eauto.
  have[wf1 wf2]:=merge_context_ok_inv mrg wf.
  have[e0[e1 e2]]:=merge_re_re mrg.
  have[s/pi_inv[/ch_inv tyA _]]:=validity wf2 tyn.
  rewrite<-e2=>//.
  move=>Γ A B m s sb tym ih tyB _ wf m0 n e; subst.
  have[G1[G2[r1[r2[A0[B0[t0]]]]]]]:=ih wf _ _ erefl.
  firstorder; subst.
  exists G1. exists G2. exists (~~r2). exists r2. exists A0. exists B0. exists t0.
  repeat split; eauto.
  apply: conv_trans; eauto.
Qed.
