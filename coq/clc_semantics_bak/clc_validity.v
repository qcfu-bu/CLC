From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
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

Theorem validity Γ m A :
  ok Γ -> Γ ⊢ m : A -> exists s l, [Γ] ⊢ A : s @ l.
Proof with eauto using clc_type, re_pure, merge_re_id.
  move=>wf tp. elim: tp wf=>{Γ m A}.
  move=>Γ s l k o.
    exists U. exists l.+2...
  move=>Γ A B s r t i k tyA ihA tyB ihB o.
    exists U. exists i.+1...
  move=>Γ x A s hs o.
    move:(has_ok o hs)=>[l tyA].
    exists s. exists l...
  move=>Γ A B m s t i k tyP ihP tym ihm o.
    exists t. exists i...
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn o.
    move:(merge_context_ok_inv mrg o)=>[o1 o2].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    move:o1=>/ihm{ihm}[r1[l1 /pi_inv[r2[l2[tyA tyB]]]]].
    destruct s.
    exists r2. exists l2.
    have {}mrg : [Γ1] ∘ Γ2 => [Γ].
      replace Γ2 with [Γ2].
      rewrite e2 e3...
      rewrite<-pure_re...
    by apply: (substitution tyB k mrg tyn).
    exists r2. exists l2.
    move:(substitutionN tyB tyn).
    by rewrite e2.
  move=>Γ k o. exists U. exists 1...
  move=>Γ k o. exists U. exists 0...
  move=>Γ A B s r t i leq k tyA ihA tyB ihB o.
    exists U. exists i.+1...
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg
    tyS ihS tym ihm tyn ihn o.
    exists t. exists i...
  move=>Γ1 Γ2 Γ m n A mrg _ _ tyn ihn o.
    move:(merge_context_ok_inv mrg o)=>[_/ihn[x[l tyA]]]{ihn}.
    move:(merge_re_re mrg)=>[_[_ e]].
    exists x. exists l.
    by rewrite<-e.
  move=>Γ1 Γ2 Γ A B C m n s r t k x i leq key mrg
    tym _ tyC _ tyn _ o.
    exists x. exists i.
    move:(merge_re_re mrg)=>[e0[e1 e2]].
    destruct k; simpl in tyC.
    have mrg1:[Γ2] ∘ Γ1 => [Γ].
    rewrite e2 (pure_re key) e1.
    apply: merge_re_id.
    have:=substitution tyC key mrg1 tym.
    by asimpl.
    have:=substitutionN tyC tym.
    by rewrite e2.
  move=>Γ A B m s i sb tym ihm tyB ihB o.
    exists s. exists i...
Qed.