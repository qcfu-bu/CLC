From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution 
  cclc_ast cclc_dual cclc_typing cclc_weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subst_dual0 A B σ : dual0 A B -> dual0 A.[σ] B.[σ].
Proof with eauto using dual0.
  move=>d. elim:d σ=>{A B}.
  move=>σ. asimpl...
  move=>σ. asimpl...
  move=>A B1 B2 s d1 d2 σ. asimpl...
  move=>A B1 B2 s d1 d2 σ. asimpl...
Qed.

Lemma subst_dual A B σ : A ~ B -> A.[σ] ~ B.[σ].
Proof with eauto using dual.
  move=>d. elim:d σ=>{A B}.
  move=>A B d σ. move/subst_dual0 in d... 
  move=>A A' B' B c1 d ih c2 σ.
    apply: dual_conv.
    apply: conv_subst.
    exact: c1.
    apply: ih.
    apply: conv_subst.
    exact: c2.
Qed.

Lemma esubstitution Γ Δ p σ :
  Γ ⊢ p -> Δ ⊢ σ ⊣ Γ -> Δ ⊢ p.[σ].
Proof.
  move=>ty. elim: ty Δ σ=>{Γ p}.
  move=>Γ m A s tym Δ σ agr; asimpl.
    econstructor.
    apply: esubstitution; eauto.
  move=>Γ1 Γ2 Γ p q mrg typ ihp tyq ihq Δ σ agr; asimpl.
    have[G1[G2[mrg1[agr1 agr2]]]]:=merge_agree_subst_inv agr mrg.
    econstructor; eauto.
  move=>Γ p A B i d tyA tyB typ ihp Δ σ agr; asimpl.
    have d':=subst_dual σ d.
    econstructor.
    apply: d'.
    have tyA':=esubstitution tyA (agree_subst_re agr).
    asimpl in tyA'; eauto.
    have tyB':=esubstitution tyB (agree_subst_re agr).
    asimpl in tyB'; eauto.
    asimpl.
    apply: ihp.
    have:
      (Ch A.[ren (+1)]).[up σ] :L (Ch B).[σ] :L Δ ⊢ up (up σ) ⊣
      Ch A.[ren (+1)] :L Ch B :L Γ.
      apply: agree_subst_ty.
      apply: agree_subst_ty.
      exact: agr.
    by asimpl.
Qed.

Lemma substitution Γ1 Γ2 Γ p m A s :
  A :{s} Γ1 ⊢ p ->
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ ->
  Γ2 ⊢ m : A : s ->
  Γ ⊢ p.[m/].
Proof with eauto.
  move=>typ k mrg tym.
  apply: esubstitution...
  destruct s.
  { apply: agree_subst_wkU.
    move:(merge_pureR mrg k)=>->...
    move:(merge_re_re mrg)=>[_[_<-]].
    rewrite<-pure_re...
    by asimpl. }
  { apply: agree_subst_wkL...
    by asimpl. }
Qed.

Lemma substitution2 Γ1 Γ2 Γ3 Γ4 Γ m1 m2 p A B s r :
  B :{r} A :{s} Γ1 ⊢ p ->
  Γ2 |> s ->
  Γ3 |> r ->
  Γ1 ∘ Γ2 => Γ4 -> Γ3 ∘ Γ4 => Γ ->
  Γ2 ⊢ m1 : A : s ->
  Γ3 ⊢ m2 : B.[m1/] : r ->
  Γ ⊢ p.[m2,m1/].
Proof.
  move=>typ k1 k2 mrg1 mrg2 ty1 ty2.
  apply: esubstitution.
  exact: typ.
  move:(merge_re_re mrg1)=>[e0[e1 e2]].
  move:(merge_re_re mrg2)=>[e3[e4 e5]].
  destruct r; destruct s.
  { apply: agree_subst_wkU.
    apply: agree_subst_wkU.
    have e:=merge_pureR mrg1 k1; subst.
    have e:=merge_pureL mrg2 k2; subst.
    eauto. asimpl.
    rewrite<-e5. rewrite<-e2.
    by rewrite<-pure_re.
    rewrite<-e5. rewrite<-e3.
    by rewrite<-pure_re. }
  { have[G[mrg3 mrg4]]:=merge_splitR (merge_sym mrg2) mrg1. 
    apply: agree_subst_wkU.
    apply: agree_subst_wkL.
    exact: mrg4. eauto.
    have e:=merge_pureR mrg3 k2; subst.
    by asimpl.
    rewrite<-e4. by rewrite<-pure_re. }
  { have[G[mrg3 mrg4]]:=merge_splitR (merge_sym mrg2) mrg1. 
    apply: agree_subst_wkL.
    exact: mrg4.
    apply: agree_subst_wkU.
    eauto. asimpl.
    rewrite e0. by rewrite<-pure_re.
    have e:=merge_pureL mrg3 k1; subst.
    eauto. }
  { apply: agree_subst_wkL.
    apply: merge_sym.
    exact: mrg2.
    apply: agree_subst_wkL; eauto.
    by asimpl.
    eauto. }
Qed.

Lemma substitutionN Γ1 Γ2 p m A s :
  _: Γ1 ⊢ p -> Γ2 ⊢ m : A : s -> Γ1 ⊢ p.[m/].
Proof with eauto.
  move=>typ tym.
  apply: esubstitution...
  apply: agree_subst_wkN...
Qed.

Lemma strengthen Γ p : _: Γ ⊢ p.[ren (+1)] -> Γ ⊢ p.
Proof with eauto using key.
  move=>typ.
  have ty : (nil ⊢ U @ 0 : U @ 1 : U).
  apply: clc_axiom...
  have := (substitutionN typ ty).
  rewrite proc_subst_comp.
  asimpl.
  rewrite proc_ids...
Qed.
