From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening cclc_ast cclc_dual cclc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rename_dual0 A B ξ : dual0 A B -> dual0 A.[ren ξ] B.[ren ξ].
Proof with eauto using dual0.
  move=>d. elim:d ξ=>{A B}.
  move=>ξ. asimpl...
  move=>ξ. asimpl...
  move=>A B1 B2 s d1 d2 ξ. asimpl...
  move=>A B1 B2 s d1 d2 ξ. asimpl...
Qed.

Lemma rename_dual A B ξ : A ~ B -> A.[ren ξ] ~ B.[ren ξ].
Proof with eauto using dual.
  move=>d. elim:d ξ=>{A B}.
  move=>A B d ξ. move/rename_dual0 in d... 
  move=>A A' B' B c1 d ih c2 ξ.
    apply: dual_conv.
    apply: conv_subst.
    exact: c1.
    apply: ih.
    apply: conv_subst.
    exact: c2.
Qed.

Lemma rename_ok Γ Γ' p ξ :
  Γ ⊢ p -> agree_ren ξ Γ Γ' -> Γ' ⊢ p.[ren ξ].
Proof.
  move=>tp. elim: tp Γ' ξ=>{Γ p}.