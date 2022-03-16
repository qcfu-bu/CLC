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
  move=>Γ m A s tym Γ' ξ agr; asimpl.
    econstructor.
    apply: clc_weakening.rename_ok.
    exact: tym.
    exact: agr.
  move=>Γ1 Γ2 Γ p q mrg typ ihp tyq ihq Γ' ξ agr; asimpl.
    have[G1[G2[mrg1[agr1 agr2]]]]:=merge_agree_ren_inv agr mrg.
    econstructor.
    exact: mrg1.
    apply: ihp.
    exact: agr1.
    apply: ihq.
    exact: agr2.
  move=>Γ p A B d typ ihp Γ' ξ agr; asimpl.
    have d':=rename_dual ξ d.
    econstructor.
    apply: d'.
    asimpl.
    apply: ihp.
    have: 
      (agree_ren (upren (upren ξ))
        (Ch A.[ren (+1)] :L Ch B :L Γ)
        (Ch A.[ren (+1)].[ren (upren ξ)] :L Ch B.[ren ξ] :L Γ')).
      econstructor.
      econstructor.
      exact:agr.
    by asimpl.
Qed.

Lemma weakeningU Γ p A : Γ ⊢ p -> A :U Γ ⊢ p.[ren (+1)].
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma weakeningN Γ p : Γ ⊢ p -> _: Γ ⊢ p.[ren (+1)].
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma eweakeningU Γ p p' A :
  p' = p.[ren (+1)]%P -> Γ ⊢ p -> A :U Γ ⊢ p'.
Proof.  
  move=>*; subst. by apply: weakeningU.
Qed.

Lemma eweakeningN Γ p p' :
  p' = p.[ren (+1)]%P -> Γ ⊢ p -> _: Γ ⊢ p'.
Proof.  
  move=>*; subst. by apply weakeningN.
Qed.