From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_typing
  clc_weakening clc_substitution clc_inversion.

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

Theorem validity Γ m A s :
  ok Γ -> Γ ⊢ m : A : s -> [Γ] ⊢ A : Sort s : U.
Proof with eauto using clc_type, re_pure, merge_re_id, key.
  move=>wf tp. elim: tp wf=>{Γ m A s}.
  move=>Γ s k o...
  move=>Γ A B s r t k tyA ihA tyB ihB o...
  move=>Γ x A s hs o. move:(has_ok o hs)=>tyA...
  move=>Γ A B m s r t k tyP ihP tym ihm o...
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn o.
    move:(merge_context_ok_inv mrg o)=>[o1 o2].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    move:o1=>/ihm{ihm}/pi_inv[tyA[_ tyB]].
    destruct s.
    have {}mrg : [Γ1] ∘ Γ2 => [Γ].
      replace Γ2 with [Γ2].
      rewrite e2 e3...
      rewrite<-pure_re...
    simpl in tyB. rewrite<-re_invo in tyB.
    by apply: (substitution tyB k mrg tyn).
    simpl in tyB. rewrite<-re_invo in tyB.
    have:=substitutionN tyB tyn.
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
    have//:=substitution tyA k mrg tym.
    have:=substitutionN tyA tym.
    by rewrite e2.
  move=>Γ1 Γ2 Γ m n A s mrg _ _ tyn ihn o.
    move:(merge_context_ok_inv mrg o)=>[_/ihn tyA]{ihn}.
    move:(merge_re_re mrg)=>[_[_ e]].
    by rewrite<-e.
  move=>Γ1 Γ2 Γ A B C m n s r t k x leq key mrg
    tym _ tyC _ tyn _ o.
    move:(merge_re_re mrg)=>[e0[e1 e2]].
    destruct k; simpl in tyC.
    have mrg1:[Γ2] ∘ Γ1 => [Γ].
    rewrite e2 (pure_re key) e1.
    apply: merge_re_id. inv leq.
    have:=substitution tyC key mrg1 tym.
    by asimpl.
    have:=substitutionN tyC tym.
    by rewrite e2.
  move=>Γ k wf...
  move=>Γ k o...
  move=>Γ r k o...
  move=>Γ r A B s k tyA ihA tyB ihB o...
  move=>Γ r A k tyA ihA o...
  move=>Γ1 Γ2 r1 r2 Γ m n A B s t mrg d tyA _ _ _ _ _ wf.
    have[_[e1 e2]]:=merge_re_re mrg.
    econstructor; simpl...
    constructor.
  move=>Γ r1 r2 A B m s xor tym ihm o.
    have/ch_inv/act_inv[tyA[_ tyB]]:=ihm o.
    apply: clc_sigma...
    destruct s; simpl; constructor.
  move=>Γ r1 r2 A B m s xor tym ihm o.
    have/ch_inv/act_inv[tyA[_ tyB]]:=ihm o.
    apply: clc_pi...
  move=>Γ r1 r2 m xor tym ihm o...
  move=>Γ r1 r2 m xor tym ihm o...
  move=>Γ A B m s sb tym ihm tyB ihB o...
Qed.
