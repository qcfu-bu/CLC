From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_ty Γ Γ' ξ m s :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m :{s} Γ) (m.[ren ξ] :{s} Γ')
| agree_ren_n Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (_: Γ) (_: Γ')
| agree_ren_wkU Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (ξ >>> (+1)) (Γ) (m :U Γ')
| agree_ren_wkN Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (ξ >>> (+1)) (Γ) (_: Γ').

Lemma agree_ren_refl Γ : agree_ren id Γ Γ.
Proof with eauto using agree_ren.
  elim: Γ...
  move=>[[A s]|] Γ ih.
  have:(agree_ren (upren id) (A :{s} Γ) (A.[ren id] :{s} Γ))...
  by asimpl.
  have:(agree_ren (upren id) (_: Γ) (_: Γ))...
  by asimpl.
Qed.

Lemma agree_ren_key Γ Γ' ξ s : 
  agree_ren ξ Γ Γ' -> Γ |> s -> Γ' |> s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ Γ' ξ}...
  move=>Γ Γ' ξ m s agr ih t k.
  inv k...
  move=>Γ Γ' ξ agr ih t k.
  inv k...
  move=>Γ Γ' ξ m agr ih [] /ih k...
Qed.

Lemma agree_ren_re_re Γ Γ' ξ :
  agree_ren ξ Γ Γ' -> agree_ren ξ [Γ] [Γ'].
Proof with eauto using agree_ren.
  elim=>{Γ Γ' ξ}... move=>Γ Γ' ξ m[]...
Qed.

Lemma agree_ren_has Γ Γ' ξ x s A :
  agree_ren ξ Γ Γ' ->
  has Γ x s A -> has Γ' (ξ x) s A.[ren ξ].
Proof with eauto using agree_ren_key.
  move=>agr. elim: agr x s A=>{Γ Γ' ξ}.
  move=>ξ x s A hs. inv hs.
  move=>Γ Γ' ξ m s agr ih x t A hs. 
    inv hs; asimpl.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
    replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
  move=>Γ Γ' ξ agr ih x s A hs.
    inv hs; asimpl.
    replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
  move=>Γ Γ' ξ m agr ih x s A /ih hs.
    asimpl.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
  move=>Γ Γ' ξ agr ih x s A /ih hs.
    asimpl.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)]
      by autosubst.
    constructor...
Qed.

Lemma merge_agree_ren_inv Γ Γ' Γ1 Γ2 ξ :
  agree_ren ξ Γ Γ' -> merge Γ1 Γ2 Γ ->
  exists Γ1' Γ2',
    merge Γ1' Γ2' Γ' /\
    agree_ren ξ Γ1 Γ1' /\
    agree_ren ξ Γ2 Γ2'.
Proof with eauto 6 using merge, agree_ren.
  move=>agr. elim: agr Γ1 Γ2=>{Γ Γ' ξ}.
  move=>ξ Γ1 Γ2 mrg. inv mrg.
    exists nil. exists nil...
  move=>Γ Γ' ξ m s agr ih Γ1 Γ2 mrg. inv mrg.
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
      exists (m.[ren ξ] :U G1).
      exists (m.[ren ξ] :U G2)...
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
      exists (m.[ren ξ] :L G1).
      exists (_: G2)...
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
      exists (_: G1).
      exists (m.[ren ξ] :L G2)...
  move=>Γ Γ' ξ agr ih Γ1 Γ2 mrg. inv mrg.
    move:H2=>/ih[G1[G2[mrg[agr1 agr2]]]]{ih}.
    exists (_: G1).
    exists (_: G2)...
  move=>Γ Γ' ξ m agr ih Γ1 Γ2 /ih[G1[G2[mrg[agr1 agr2]]]].
    exists (m :U G1).
    exists (m :U G2)...
  move=>Γ Γ' ξ agr ih Γ1 Γ2 /ih[G1[G2[mrg[agr1 agr2]]]].
    exists (_: G1).
    exists (_: G2)...
Qed.

Lemma rename_ok Γ Γ' m A ξ :
  Γ ⊢ m : A -> agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using clc_type, agree_ren, agree_ren_key.
  move=>ty. elim: ty Γ' ξ=>{Γ m A}.
  move=>Γ s l k Γ' ξ agr. asimpl...
  move=>Γ A B [] r t i k tyA ihA tyB ihB Γ' ξ agr.
  { asimpl.
    apply: clc_pi...
    apply: ihB=>//=.
    constructor.
    rewrite<-!pure_re... }
  { asimpl.
    apply: clc_pi...
    apply: ihB=>//=.
    constructor.
    rewrite<-!pure_re... }
  move=>Γ x A s hs Γ' ξ agr.
  { asimpl. 
    apply: clc_var.
    apply: agree_ren_has... }
  move=>Γ A B m s r t i k tyP ihP tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_lam...
    move:(ihP _ _ (agree_ren_re_re agr)). 
    asimpl... }
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn Γ' ξ agr.
  { asimpl.
    move:(merge_agree_ren_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(ihm _ _ agr1)=>{ihm}tym.
    move:(ihn _ _ agr2)=>{ihn}tyn.
    move:(agree_ren_key agr2 k)=>{}k.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    apply: clc_app...
    asimpl in tym... }
  move=>Γ A B m s i sb tym ihm tyB ihB Γ' ξ agr.
  { move:(ihm _ _ agr)=>{ihm}tym.
    move:(ihB _ _ (agree_ren_re_re agr))=>{ihB}tyB.
    apply: clc_conv.
    apply: sub_subst...
    by apply: tym.
    by apply: tyB. }
Qed.

Lemma has_ok Γ x A s :
  ok Γ -> has Γ x s A -> exists l, [Γ] ⊢ A : s @ l.
Proof with eauto using agree_ren, agree_ren_refl.
  move=> wf. elim: wf s x A=>{Γ}.
  move=>s x A hs. inv hs.
  move=>Γ A s l wf ih tyA t x B hs. inv hs.
  { exists l.
    replace (t @ l) with (t @ l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    destruct t; simpl... }
  { move:H5=>/ih{ih}[i ty].
    exists i.
    replace (t @ i) with (t @ i).[ren (+1)] by autosubst.
    apply: rename_ok; eauto... }
  move=>Γ wf ih s x A hs. inv hs.
  { move:H0=>/ih{ih}[i ty].
    exists i.
    replace (s @ i) with (s @ i).[ren (+1)] by autosubst.
    apply: rename_ok; eauto... }
Qed.

Lemma weakeningU Γ m A B :
  Γ ⊢ m : A -> B :U Γ ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma weakeningN Γ m A :
  Γ ⊢ m : A -> _: Γ ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma eweakeningU Γ m m' A A' B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A -> B :U Γ ⊢ m' : A'.
Proof.  
  move=>*; subst. by apply: weakeningU.
Qed.

Lemma eweakeningN Γ m m' A A' :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A -> _: Γ ⊢ m' : A'.
Proof.  
  move=>*; subst. by apply weakeningN.
Qed.