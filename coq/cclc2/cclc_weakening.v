From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_typing
  clc_weakening cclc_ast cclc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  move=>Γ p r1 r2 A d tyA typ ihp Γ' ξ agr; asimpl.
    econstructor; eauto.
    have tyA':=rename_ok tyA (agree_ren_re_re agr).
    asimpl in tyA'; eauto.
    asimpl.
    apply: ihp.
    have: 
      (agree_ren (upren (upren ξ))
        (Ch r1 A.[ren (+1)] :L Ch r2 A :L Γ)
        (Ch r1 A.[ren (+1)].[ren (upren ξ)] :L Ch r2 A.[ren ξ] :L Γ')).
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
