From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma iget_Forall i P C Cs:
  iget i Cs C -> List.Forall (fun C => P C) Cs -> P C.
Proof.
  elim=>{i C Cs}.
  move=> C Cs tyCs. by inv tyCs.
  move=> i C C' Cs ig ih tyCs.
    inv tyCs.
    apply: ih; eauto.
Qed.

Inductive arity_spine : 
  context term -> term -> list term -> term -> Prop :=
| arity_spine_nil Γ A s l :
  pure Γ ->
  [ Γ |- A :- Sort s l ] ->
  arity_spine Γ A nil A
| arity_spine_u_Arrow_cons Γ1 Γ2 Γ hd tl A B B' l :
  pure Γ1 ->
  [ Γ1 |- Arrow A B U :- Sort U l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ2 B.[hd/] tl B' ->
  arity_spine Γ (Arrow A B U) (hd :: tl) B'
| arity_spine_l_Arrow_cons Γ1 Γ2 Γ hd tl A B B' l :
  [ re Γ1 |- Arrow A B L :- Sort U l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ2 B.[hd/] tl B' ->
  arity_spine Γ (Arrow A B L) (hd :: tl) B'
| arity_spine_u_Lolli_cons Γ1 Γ2 Γ hd tl A B B' l :
  pure Γ1 ->
  [ Γ1 |- Lolli A B U :- Sort L l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ2 B.[hd/] tl B' ->
  arity_spine Γ (Lolli A B U) (hd :: tl) B'
| arity_spine_l_Lolli_cons Γ1 Γ2 Γ hd tl A B B' l :
  [ re Γ1 |- Lolli A B L :- Sort L l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ2 B.[hd/] tl B' ->
  arity_spine Γ (Lolli A B L) (hd :: tl) B'.

Lemma App_arity_spine Γ1 Γ2 Γ m ms A B :
  [ Γ1 |- m :- A ] ->
  arity_spine Γ2 A ms B ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- spine m ms :- B ].
Proof.
  move=> tyM tsp. elim: tsp Γ1 Γ m tyM=>//={Γ2 A ms B}.
  move=> Γ2 A s l p tyA Γ1 Γ m tyM mg.
    move: (merge_pure2 mg p)=>->//=.
  move=> Γ1 Γ2 Γ hd tl A B B' l p 
    tyArrow tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Arrow_App; eauto.
    move: (merge_re2 Γ1').
    rewrite e1'.
    rewrite <- e2'.
    rewrite <- e1.
    rewrite <- pure_re; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l 
    tyArrow tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[ΓX[mg1 mg2]].
    apply: ih; eauto.
    apply: l_Arrow_App; eauto.
    apply: merge_sym; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l p 
    tyLolli tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Lolli_App; eauto.
    move: (merge_re2 Γ1').
    rewrite e1'.
    rewrite <- e2'.
    rewrite <- e1.
    rewrite <- pure_re; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l 
    tyLolli tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[ΓX[mg1 mg2]].
    apply: ih; eauto.
    apply: l_Lolli_App; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_arity1_ok Γ A B s s' t l :
  [ Γ |- A :- B ] -> 
  B <: s @ l ->
  arity s' A ->
  exists t', 
    [ Γ |- arity1 t A :- t' @ l ].
Proof.
  move=> ty. elim: ty s s' t l; intros;
  match goal with
  | [ H : arity _ _ |- _ ] => try solve [inv H]
  end=>//=.
  exists U. 
    move: H0=>/sub_Sort_inv[_ lt].
    have sb : U @ l.+1 <: U @ l0.
      apply: sub_Sort; eauto.
    apply: s_Conv.
    apply: sb.
    constructor.
    apply re_pure.
    constructor; eauto.
  inv H5.
    have sb : s @ l <: s @ l by eauto.
    move: (H3 s s' t l sb H7)=>[t' ty].
    exists U.
    move: H4=>/sub_Sort_inv[_ lte].
    apply: u_Arrow; eauto.
    apply: s_Conv.
    apply: sub_Sort; eauto.
    constructor.
    apply re_pure.
    apply H0.
    apply: s_Conv.
    apply: sub_Sort; eauto.
    constructor.
    apply re_pure.
    apply ty.
  apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma arity_arity2_ok Γ A B I s t l :
  [ Γ |- A :- B ] ->
  B <: s @ l ->
  arity U A ->
  [ Γ |- I :- A ] ->
  exists t', 
    [ Γ |- arity2 t I A :- t' @ l ].
Proof.
  move=> ty. elim: ty s t l I; intros;
  match goal with
  | [ H : arity _ _ |- _ ] => try solve [inv H]
  end=>//=.
  exists U.
    move: H0=>/sub_Sort_inv[_ lt]. inv H1.
    have sb1 : U @ l <: U @ l0.
      apply: sub_Sort; eauto.
    have sb2 : U @ l.+1 <: U @ l0.
      apply: sub_Sort; eauto.
    apply: u_Arrow; eauto.
    apply: s_Conv.
    apply: sb1.
    constructor. apply re_pure.
    apply: H2.
    apply: s_Conv.
    apply: sb2.
    constructor. apply re_pure.
    repeat constructor; eauto.
  inv H5.
    have sb : s @ l <: s @ l by eauto.
    have ty0 : [ A0 +u Γ0 |- Var 0 :- A0.[ren (+1)] ].
      apply: u_Var.
      constructor; eauto.
    have //=tyIw : [ A0 +u Γ0 |- I.[ren (+1)] :- (Arrow A0 B0 U).[ren (+1)] ].
      apply: eweakeningU; eauto.
    have p2 : pure (A0 +u Γ0) by constructor.
    have mg : merge (A0 +u Γ0) (A0 +u Γ0) (A0 +u Γ0).
      constructor.
      apply: merge_pure; eauto.
    move: (u_Arrow_App p2 tyIw ty0 mg); asimpl=> tyIx.
    move: (H3 s t l _ sb H8 tyIx)=>[t' ty].
    exists U.
    move: H4=>/sub_Sort_inv[_ lt].
    have sbx : U @ l <: U @ l0.
      apply: sub_Sort; eauto.
    apply: s_Conv.
    apply: sbx.
    constructor. apply: re_pure.
    apply: u_Arrow; eauto.
  apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma arity1_spine Γ ms A s s' t l :
  arity_spine Γ A ms (Sort s l) ->
  arity s' A ->
  pure Γ ->
  arity_spine Γ (arity1 t A) ms (Sort t l).
Proof.
  move e:(Sort s l)=> n tsp. 
  elim: tsp s l e t=>//={Γ n A ms}.
  move=> Γ A s l p tyA s0 l0 e t a _; subst.
    inv a=>//=.
    apply: arity_spine_nil; eauto.
    constructor; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l _
    tyArrow tyHd mg sp ih s0 l0 e t a p'; subst.
    inv a=>//=.
    move: (merge_pure_inv mg p')=>[p1 p2].
    move: (merge_pure1 mg p1)=>e1.
    move: (merge_pure2 mg p2)=>e2.
    subst.
    have e : s0 @ l0 = s0 @ l0 by eauto.
    have a : arity s' B.[hd/].
      apply: arity_subst; eauto.
    move: (ih s0 l0 e t a)=> h.
    apply u_Arrow_inv in tyArrow; firstorder.
    have sb : x @ x0 <: x @ x0 by eauto.
    move: (arity_arity1_ok t H1 sb H0)=>[t' ty].
    apply: arity_spine_u_Arrow_cons; eauto.
    apply: u_Arrow; eauto.
    erewrite arity1_subst; eauto.
  intros. inv H4.
  intros. inv H5.
  intros. inv H4.
Qed.

Lemma arity2_spine Γ ms I A s t l :
  arity_spine Γ A ms (Sort s l) ->
  arity U A ->
  pure Γ ->
  [ Γ |- I :- A ] ->
  arity_spine Γ 
    (arity2 t I A) ms (Arrow (spine I ms) (Sort t l) U).
Proof.
  move e:(Sort s l)=> n tsp. 
  elim: tsp I s l e t=>//={Γ n A ms}.
  move=> Γ A s l p tyA I s0 l0 e t a _ tyI; subst.
    inv a=>//=.
    have sb : U @ l0 <: U @ l0.+1.
      by apply: sub_Sort.
    apply: arity_spine_nil; eauto.
    apply: u_Arrow.
    apply: p.
    apply: s_Conv.
    apply: sb.
    constructor; eauto.
    apply: re_pure.
    apply: tyI.
    constructor; eauto.
    constructor; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l p
    tyArrow tyHd mg sp ih I s0 l0 e t a p' tyI; subst.
    inv a=>//=.
    move: (merge_pure_inv mg p')=>[p1 p2].
    move: (merge_pure1 mg p1)=>e1.
    move: (merge_pure2 mg p2)=>e2.
    subst.
    have e : s0 @ l0 = s0 @ l0 by eauto.
    have a : arity U B.[hd/].
      apply: arity_subst; eauto.
    have ty : [ Γ1 |- App I hd :- B.[hd/] ].
      apply: u_Arrow_App; eauto.
    move: (ih (App I hd) s0 l0 e t a p ty)=> h.
    apply u_Arrow_inv in tyArrow; firstorder.
    have sb : x @ x0 <: x @ x0 by eauto.
    have pA : pure (A +u Γ1).
      constructor; eauto.
    have //=tyI' : [ A +u Γ1 |- I.[ren (+1)] :- (Arrow A B U).[ren (+1)] ].
      apply: eweakeningU; eauto.
    have ty0 : [ A +u Γ1 |- Var 0 :- A.[ren (+1)] ].
      apply: u_Var.
      constructor; eauto.
    have mgA : merge (A +u Γ1) (A +u Γ1) (A +u Γ1).
      constructor.
      apply: merge_pure; eauto.
    move: (u_Arrow_App pA tyI' ty0 mgA); asimpl=>{pA}tyApp.
    move: (arity_arity2_ok t H1 sb H0 tyApp)=>[t' ty'].
    apply: arity_spine_u_Arrow_cons; eauto.
    apply: u_Arrow; eauto.
    erewrite arity2_subst; asimpl; eauto.
  intros. inv H4.
  intros. inv H5.
  intros. inv H4.
Qed.

Ltac solve_Ind_spine' :=
  match goal with 
  | [ H : spine' (Ind _ _ _) ?ms = _ |- _ ] =>
    induction ms; simpl; intros; discriminate
  | [ H : _ = spine' (Ind _ _ _) ?ms  |- _ ] =>
    induction ms; simpl; intros; discriminate
  end.

Lemma arity_spine_u_Arrow_rcons Γ1 Γ2 Γ A B C n ms :
  arity_spine Γ1 A ms (Arrow B C U) ->
  pure Γ2 ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Arrow B C U)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Arrow_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H3 H1)=>e2.
    destruct s.
    apply: arity_spine_u_Arrow_cons.
      apply: H.
      apply: H0.
      rewrite<-e2. rewrite e1; eauto.
      apply: H3.
      move: (substitutionU tyC H2 H1 H3)=>//=tyCN.
      apply: arity_spine_nil; eauto.
      rewrite<-e1; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Arrow_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_l_Arrow_rcons Γ1 Γ2 Γ A B C n ms :
  arity_spine Γ1 A ms (Arrow B C L) ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Arrow B C L)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Arrow_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H2)=>[e1 e2].
    destruct s.
    apply: arity_spine_l_Arrow_cons.
      2:{ apply: H1. }
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H1)=>//=tyCN.
      apply: arity_spine_nil; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_u_Arrow_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_u_Lolli_rcons Γ1 Γ2 Γ A B C n ms :
  arity_spine Γ1 A ms (Lolli B C U) ->
  pure Γ2 ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C U)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Lolli_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H3 H1)=>e2.
    destruct s.
    exfalso. apply: sub_Sort_False2; eauto.
    apply: arity_spine_u_Lolli_cons.
      apply: H.
      apply: H0.
      rewrite<-e2. rewrite e1; eauto.
      apply: H3.
      move: (substitutionU tyC H2 H1 H3)=>//=tyCN.
      apply: arity_spine_nil; eauto.
      rewrite<-e1; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Arrow_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_l_Lolli_rcons Γ1 Γ2 Γ A B C n ms :
  arity_spine Γ1 A ms (Lolli B C L) ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  arity_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C L)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Lolli_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H2)=>[e1 e2].
    destruct s.
    exfalso. apply: sub_Sort_False2; eauto.
    apply: arity_spine_l_Lolli_cons.
      2:{ apply: H1. }
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H1)=>//=tyCN.
      apply: arity_spine_nil; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_u_Arrow_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: arity_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Γ4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma s_Ind_spine'_invX Γ A B Cs ms s :
  pure Γ ->
  arity s A ->
  [ Γ |- spine' (Ind A Cs s) ms :- B ] ->
  exists A' s t l,
    arity t A' /\
    [ Γ |- A' :- s @ l ] /\
    arity_spine Γ A (rev ms) A' /\
    A' <: B.
Proof.
  move e:(spine' (Ind A Cs s) ms)=> n p a ty. 
  elim: ty A Cs ms s p a e=>{Γ n}; intros; 
  try solve [exfalso; solve_Ind_spine'].
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure1 H4 p1)=> e1.
    move: (merge_pure2 H4 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H1 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    move: sb=>/sub_Arrow_inv[e[sb _]].
    move: ty=>/u_Arrow_inv[x[lx[_[tyA1[tyB1 _]]]]].
    exists B1.[n/]. exists x. exists t'. exists lx.
    have tyN : [ Γ1 |- n :- A1 ].
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply e.
      rewrite <- pure_re; eauto.
      apply: H2.
    repeat split.
    apply: arity_subst; eauto.
    replace (x @ lx) with (x @ lx).[n/] by autosubst.
    apply: substitutionU; eauto.
    rewrite rev_cons.
    apply: arity_spine_u_Arrow_rcons; eauto.
    apply: sub_subst; eauto.
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure1 H3 p1)=> e1.
    move: (merge_pure2 H3 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H0 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    move: sb=>/sub_Arrow_inv[e[sb _]].
    move: ty=>/u_Arrow_inv[x[lx[_[tyA1[tyB1 _]]]]].
    exists B1.[n/]. exists x. exists t'. exists lx.
    have tyN : [ Γ1 |- n :- A1 ].
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply e.
      rewrite <- pure_re; eauto.
      apply: H1.
    repeat split.
    apply: arity_subst; eauto.
    replace (x @ lx) with (x @ lx).[n/] by autosubst.
    apply: substitutionU; eauto.
    rewrite rev_cons.
    apply: arity_spine_u_Arrow_rcons; eauto.
    apply: sub_subst; eauto.
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure1 H4 p1)=> e1.
    move: (merge_pure2 H4 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H1 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    exfalso; solve_sub.
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure1 H3 p1)=> e1.
    move: (merge_pure2 H3 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H0 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    exfalso; solve_sub.
  destruct ms; simpl in e.
    inv e.
    rewrite /rev/catrev.
    exists A. exists U. exists s. exists l.
    repeat split; eauto.
    apply: arity_spine_nil; eauto.
    inv e.
  move:(H3 A0 Cs ms s0 p a e)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    exists A'. exists s'. exists t'. exists l'.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma s_Ind_spine_invX Γ A B Cs ms s :
  pure Γ ->
  arity s A ->
  [ Γ |- spine (Ind A Cs s) ms :- B ] ->
  exists A' s t l,
    arity t A' /\
    [ Γ |- A' :- s @ l ] /\
    arity_spine Γ A ms A' /\
    A' <: B.
Proof.
  move=> p a ty.
  rewrite spine_spine'_rev in ty.
  apply s_Ind_spine'_invX in ty; eauto.
  rewrite revK in ty; eauto.
Qed.

Lemma s_Ind_spine_inv Γ A Cs ms s t l :
  pure Γ ->
  arity s A ->
  [ Γ |- spine (Ind A Cs s) ms :- t @ l ] ->
  exists s l, arity_spine Γ A ms (s @ l).
Proof.
  move=> p a ty.
  move: (s_Ind_spine_invX p a ty)=>[A'[s'[t'[l'[a'[tyA'[sp sb]]]]]]].
  inv a'.
  exists t'. exists l0. eauto.
  exfalso. solve_sub.
Qed.

Lemma s_Ind_spine' Γ A B Cs s ms :
  pure Γ ->
  [ Γ |- spine' (Ind A Cs s) ms :- B ] ->
  [ Γ |- Ind A Cs s :- A ].
Proof.
  move e:(spine' (Ind A Cs s) ms)=> n p ty.
  elim: ty A Cs s ms p e=>//{Γ B n}; intros; 
  try solve [destruct ms; simpl in e; try inv e].
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure2 H4 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure2 H3 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure2 H4 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure2 H3 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    econstructor; eauto.
  - destruct ms0; simpl in e; inv e.
  - destruct ms0; simpl in e; inv e.
Qed.

Lemma s_Ind_spine Γ A B Cs s ms :
  pure Γ ->
  [ Γ |- spine (Ind A Cs s) ms :- B ] ->
  [ Γ |- Ind A Cs s :- A ].
Proof.
  rewrite spine_spine'_rev=> p ty.
  by move: (s_Ind_spine' p ty).
Qed.