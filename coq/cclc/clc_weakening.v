From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_dual clc_typing.

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

Lemma rename_ok Γ Γ' m A s ξ :
  Γ ⊢ m : A : s -> agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ] : s.
Proof with eauto using 
  clc_type, agree_ren, agree_ren_key, agree_ren_re_re.
  move=>ty. elim: ty Γ' ξ=>{Γ m A s}.
  move=>Γ s l k Γ' ξ agr. asimpl...
  move=>Γ A B [] r t i k tyA ihA tyB ihB Γ' ξ agr.
  { asimpl.
    apply: clc_pi... }
  { asimpl.
    apply: clc_pi... }
  move=>Γ x A s hs Γ' ξ agr.
  { asimpl. 
    apply: clc_var.
    apply: agree_ren_has... }
  move=>Γ A B m s r t i k tyP ihP tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_lam...
    move:(ihP _ _ (agree_ren_re_re agr)). 
    asimpl... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn Γ' ξ agr.
  { asimpl.
    move:(merge_agree_ren_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(ihm _ _ agr1)=>{ihm}tym.
    move:(ihn _ _ agr2)=>{ihn}tyn.
    move:(agree_ren_key agr2 k)=>{}k.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    apply: clc_app...
    asimpl in tym... }
  move=>Γ k Γ' ξ arg. asimpl...
  move=>Γ k Γ' ξ arg. asimpl...
  move=>Γ A B s r t i leq k tyA ihA tyB ihB Γ' ξ agr.
  { asimpl.
    destruct s.
    have:agree_ren (upren ξ) (A :U [Γ]) (A.[ren ξ] :U [Γ'])...
    have:agree_ren (upren ξ) (_: [Γ]) (_: [Γ'])... }
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg 
    tyS ihS tym ihm tyn ihn Γ' ξ agr.
  { asimpl.
    move:(merge_agree_ren_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(agree_ren_key agr1 k1)=>{}k1.
    move:(agree_ren_key agr2 k2)=>{}k2.
    apply: clc_pair...
    move:(ihS _ _ (agree_ren_re_re agr)). asimpl...
    move:(ihn _ _ agr2). asimpl... }
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn ihn Γ' ξ agr.
  { asimpl.
    move:(merge_agree_ren_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(ihm _ _ agr1)=>{}ihm.
    move:(ihn _ _ agr2)=>{}ihn.
    apply: clc_letin1... }
  move=>Γ1 Γ2 Γ A B C m n s r t k x i leq key mrg 
    tym ihm tyC ihC tyn ihn Γ' ξ agr.
  { asimpl.
    move:(merge_agree_ren_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(ihm _ _ agr1)=>{ihm}tym.
    move:(agree_ren_key agr1 key)=>{}key.
    have/ihn{ihn}tyn:agree_ren (upren (upren ξ)) (B :{r} A :{s} Γ2)
      (B.[ren (upren ξ)] :{r} A.[ren ξ] :{s} G2)...
    destruct k.
    have/ihC{ihC}tyC:agree_ren (upren ξ) (Sigma A B s r t :U [Γ2])
      ((Sigma A B s r t).[ren ξ] :U [G2])...
    asimpl in tym.
    asimpl in tyC.
    replace C.[Pair (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair (Var 1) (Var 0) t .: ren (+2)]
        in tyn by autosubst.
    have:=clc_letin2 leq key mrg1 tym tyC tyn.
    by asimpl.
    have/ihC{ihC}tyC:agree_ren (upren ξ) (_: [Γ2]) (_: [G2])...
    asimpl in tym.
    asimpl in tyC.
    replace C.[Pair (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair (Var 1) (Var 0) t .: ren (+2)]
        in tyn by autosubst.
    have:=clc_letin2 leq key mrg1 tym tyC tyn.
    by asimpl. }
  move=>Γ k Γ' ξ agr.
  { asimpl... }
  move=>Γ i k Γ' ξ agr.
  { asimpl... }
  move=>Γ i k Γ' ξ agr.
  { asimpl... }
  move=>Γ i k Γ' ξ agr.
  { asimpl... }
  move=>Γ A B s i k tyA ihA tyB ihB Γ' ξ agr.
  { asimpl.
    apply: clc_inp... }
  move=>Γ A B s i k tyA ihA tyB ihB Γ' ξ agr.
  { asimpl.
    apply: clc_out... }
  move=>Γ A i k tyA ihA Γ' ξ agr.
  { asimpl.
    apply: clc_ch... }
  move=>Γ1 Γ2 Γ m n A B C s t i d mrg tyA ihA tyB ihB tym ihm tyn ihn Γ' ξ agr.
  { asimpl.
    have[G1[G2[mrg'[agr1 agr2]]]]:=merge_agree_ren_inv agr mrg.
    have//={}ihA:=ihA _ _ (agree_ren_re_re agr1).
    have//={}ihB:=ihB _ _ (agree_ren_re_re agr2).
    have//={}ihm:=ihm _ _ agr1.
    apply: clc_fork.
    apply: dual_subst.
    exact: d.
    apply: mrg'.
    exact: ihA.
    exact: ihB.
    exact: ihm.
    apply: ihn... }
  move=>Γ A B m s tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_recv.
    replace (Ch (Inp A.[ren ξ] B.[ren (upren ξ)] s))
      with (Ch (Inp A B s)).[ren ξ] 
        by autosubst.
    apply: ihm... }
  move=>Γ A B m s tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_send.
    replace (Ch (Out A.[ren ξ] B.[ren (upren ξ)] s))
      with (Ch (Out A B s)).[ren ξ] 
        by autosubst.
    apply: ihm... }
  move=>Γ m tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_close... }
  move=>Γ m tym ihm Γ' ξ agr.
  { asimpl.
    apply: clc_wait... }
  move=>Γ A B m s i sb tym ihm tyB ihB Γ' ξ agr.
  { move:(ihm _ _ agr)=>{ihm}tym.
    move:(ihB _ _ (agree_ren_re_re agr))=>{ihB}tyB.
    apply: clc_conv.
    apply: sub_subst...
    by apply: tym.
    by apply: tyB. }
Qed.

Lemma has_ok Γ x A s :
  ok Γ -> has Γ x s A -> exists l, [Γ] ⊢ A : s @ l : U.
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

Lemma weakeningU Γ m A B s :
  Γ ⊢ m : A : s -> B :U Γ ⊢ m.[ren (+1)] : A.[ren (+1)] : s.
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma weakeningN Γ m A s :
  Γ ⊢ m : A : s -> _: Γ ⊢ m.[ren (+1)] : A.[ren (+1)] : s.
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: rename_ok...
Qed.

Lemma eweakeningU Γ m m' A A' B s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A : s -> B :U Γ ⊢ m' : A' : s.
Proof.  
  move=>*; subst. by apply: weakeningU.
Qed.

Lemma eweakeningN Γ m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A : s -> _: Γ ⊢ m' : A' : s.
Proof.  
  move=>*; subst. by apply weakeningN.
Qed.
