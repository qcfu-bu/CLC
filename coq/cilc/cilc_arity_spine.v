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
| arity_spine_nil Gamma A s l :
  pure Gamma ->
  [ Gamma |- A :- Sort s l ] ->
  arity_spine Gamma A nil A
| arity_spine_u_Prod_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  pure Gamma1 ->
  [ Gamma1 |- Prod A B U :- Sort U l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Prod A B U) (hd :: tl) B'
| arity_spine_l_Prod_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  [ re Gamma1 |- Prod A B L :- Sort U l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Prod A B L) (hd :: tl) B'
| arity_spine_u_Lolli_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  pure Gamma1 ->
  [ Gamma1 |- Lolli A B U :- Sort L l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Lolli A B U) (hd :: tl) B'
| arity_spine_l_Lolli_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  [ re Gamma1 |- Lolli A B L :- Sort L l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Lolli A B L) (hd :: tl) B'.

Lemma App_arity_spine Gamma1 Gamma2 Gamma m ms A B :
  [ Gamma1 |- m :- A ] ->
  arity_spine Gamma2 A ms B ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- spine m ms :- B ].
Proof.
  move=> tyM tsp. elim: tsp Gamma1 Gamma m tyM=>//={Gamma2 A ms B}.
  move=> Gamma2 A s l p tyA Gamma1 Gamma m tyM mg.
    move: (merge_pure2 mg p)=>->//=.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p 
    tyProd tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Prod_App; eauto.
    move: (merge_re2 Gamma1').
    rewrite e1'.
    rewrite <- e2'.
    rewrite <- e1.
    rewrite <- pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l 
    tyProd tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[GammaX[mg1 mg2]].
    apply: ih; eauto.
    apply: l_Prod_App; eauto.
    apply: merge_sym; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p 
    tyLolli tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Lolli_App; eauto.
    move: (merge_re2 Gamma1').
    rewrite e1'.
    rewrite <- e2'.
    rewrite <- e1.
    rewrite <- pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l 
    tyLolli tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[GammaX[mg1 mg2]].
    apply: ih; eauto.
    apply: l_Lolli_App; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_arity1_ok Gamma A B s s' t l :
  [ Gamma |- A :- B ] -> 
  B <: s @ l ->
  arity s' A ->
  exists t', 
    [ Gamma |- arity1 t A :- t' @ l ].
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
    apply: u_Prod; eauto.
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

Lemma arity_arity2_ok Gamma A B I s t l :
  [ Gamma |- A :- B ] ->
  B <: s @ l ->
  arity U A ->
  [ Gamma |- I :- A ] ->
  exists t', 
    [ Gamma |- arity2 t I A :- t' @ l ].
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
    apply: u_Prod; eauto.
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
    have ty0 : [ A0 +u Gamma0 |- Var 0 :- A0.[ren (+1)] ].
      apply: u_Var.
      constructor; eauto.
    have //=tyIw : [ A0 +u Gamma0 |- I.[ren (+1)] :- (Prod A0 B0 U).[ren (+1)] ].
      apply: eweakeningU; eauto.
    have p2 : pure (A0 +u Gamma0) by constructor.
    have mg : merge (A0 +u Gamma0) (A0 +u Gamma0) (A0 +u Gamma0).
      constructor.
      apply: merge_pure; eauto.
    move: (u_Prod_App p2 tyIw ty0 mg); asimpl=> tyIx.
    move: (H3 s t l _ sb H8 tyIx)=>[t' ty].
    exists U.
    move: H4=>/sub_Sort_inv[_ lt].
    have sbx : U @ l <: U @ l0.
      apply: sub_Sort; eauto.
    apply: s_Conv.
    apply: sbx.
    constructor. apply: re_pure.
    apply: u_Prod; eauto.
  apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma arity1_spine Gamma ms A s s' t l :
  arity_spine Gamma A ms (Sort s l) ->
  arity s' A ->
  pure Gamma ->
  arity_spine Gamma (arity1 t A) ms (Sort t l).
Proof.
  move e:(Sort s l)=> n tsp. 
  elim: tsp s l e t=>//={Gamma n A ms}.
  move=> Gamma A s l p tyA s0 l0 e t a _; subst.
    inv a=>//=.
    apply: arity_spine_nil; eauto.
    constructor; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l _
    tyProd tyHd mg sp ih s0 l0 e t a p'; subst.
    inv a=>//=.
    move: (merge_pure_inv mg p')=>[p1 p2].
    move: (merge_pure1 mg p1)=>e1.
    move: (merge_pure2 mg p2)=>e2.
    subst.
    have e : s0 @ l0 = s0 @ l0 by eauto.
    have a : arity s' B.[hd/].
      apply: arity_subst; eauto.
    move: (ih s0 l0 e t a)=> h.
    apply u_Prod_inv in tyProd; firstorder.
    have sb : x @ x0 <: x @ x0 by eauto.
    move: (arity_arity1_ok t H1 sb H0)=>[t' ty].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: u_Prod; eauto.
    erewrite arity1_subst; eauto.
  intros. inv H4.
  intros. inv H5.
  intros. inv H4.
Qed.

Lemma arity2_spine Gamma ms I A s t l :
  arity_spine Gamma A ms (Sort s l) ->
  arity U A ->
  pure Gamma ->
  [ Gamma |- I :- A ] ->
  arity_spine Gamma 
    (arity2 t I A) ms (Prod (spine I ms) (Sort t l) U).
Proof.
  move e:(Sort s l)=> n tsp. 
  elim: tsp I s l e t=>//={Gamma n A ms}.
  move=> Gamma A s l p tyA I s0 l0 e t a _ tyI; subst.
    inv a=>//=.
    have sb : U @ l0 <: U @ l0.+1.
      by apply: sub_Sort.
    apply: arity_spine_nil; eauto.
    apply: u_Prod.
    apply: p.
    apply: s_Conv.
    apply: sb.
    constructor; eauto.
    apply: re_pure.
    apply: tyI.
    constructor; eauto.
    constructor; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p
    tyProd tyHd mg sp ih I s0 l0 e t a p' tyI; subst.
    inv a=>//=.
    move: (merge_pure_inv mg p')=>[p1 p2].
    move: (merge_pure1 mg p1)=>e1.
    move: (merge_pure2 mg p2)=>e2.
    subst.
    have e : s0 @ l0 = s0 @ l0 by eauto.
    have a : arity U B.[hd/].
      apply: arity_subst; eauto.
    have ty : [ Gamma1 |- App I hd :- B.[hd/] ].
      apply: u_Prod_App; eauto.
    move: (ih (App I hd) s0 l0 e t a p ty)=> h.
    apply u_Prod_inv in tyProd; firstorder.
    have sb : x @ x0 <: x @ x0 by eauto.
    have pA : pure (A +u Gamma1).
      constructor; eauto.
    have //=tyI' : [ A +u Gamma1 |- I.[ren (+1)] :- (Prod A B U).[ren (+1)] ].
      apply: eweakeningU; eauto.
    have ty0 : [ A +u Gamma1 |- Var 0 :- A.[ren (+1)] ].
      apply: u_Var.
      constructor; eauto.
    have mgA : merge (A +u Gamma1) (A +u Gamma1) (A +u Gamma1).
      constructor.
      apply: merge_pure; eauto.
    move: (u_Prod_App pA tyI' ty0 mgA); asimpl=>{pA}tyApp.
    move: (arity_arity2_ok t H1 sb H0 tyApp)=>[t' ty'].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: u_Prod; eauto.
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

Lemma arity_spine_u_Prod_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Prod B C U) ->
  pure Gamma2 ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Prod B C U)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Prod_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H3 H1)=>e2.
    destruct s.
    apply: arity_spine_u_Prod_cons.
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
    apply: arity_spine_u_Prod_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
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
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_l_Prod_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Prod B C L) ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Prod B C L)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Prod_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H2)=>[e1 e2].
    destruct s.
    apply: arity_spine_l_Prod_cons.
      2:{ apply: H1. }
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H1)=>//=tyCN.
      apply: arity_spine_nil; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_u_Lolli_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Lolli B C U) ->
  pure Gamma2 ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C U)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
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
    apply: arity_spine_u_Prod_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
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
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_l_Lolli_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Lolli B C L) ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C L)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
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
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma s_Ind_spine'_invX Gamma A B Cs ms s :
  pure Gamma ->
  arity s A ->
  [ Gamma |- spine' (Ind A Cs s) ms :- B ] ->
  exists A' s t l,
    arity t A' /\
    [ Gamma |- A' :- s @ l ] /\
    arity_spine Gamma A (rev ms) A' /\
    A' <: B.
Proof.
  move e:(spine' (Ind A Cs s) ms)=> n p a ty. 
  elim: ty A Cs ms s p a e=>{Gamma n}; intros; 
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
    move: sb=>/sub_Prod_inv[e[sb _]].
    move: ty=>/u_Prod_inv[x[lx[_[tyA1[tyB1 _]]]]].
    exists B1.[n/]. exists x. exists t'. exists lx.
    have tyN : [ Gamma1 |- n :- A1 ].
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply e.
      rewrite <- pure_re; eauto.
      apply: H2.
    repeat split.
    apply: arity_subst; eauto.
    replace (x @ lx) with (x @ lx).[n/] by autosubst.
    apply: substitutionU; eauto.
    rewrite rev_cons.
    apply: arity_spine_u_Prod_rcons; eauto.
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
    move: sb=>/sub_Prod_inv[e[sb _]].
    move: ty=>/u_Prod_inv[x[lx[_[tyA1[tyB1 _]]]]].
    exists B1.[n/]. exists x. exists t'. exists lx.
    have tyN : [ Gamma1 |- n :- A1 ].
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply e.
      rewrite <- pure_re; eauto.
      apply: H1.
    repeat split.
    apply: arity_subst; eauto.
    replace (x @ lx) with (x @ lx).[n/] by autosubst.
    apply: substitutionU; eauto.
    rewrite rev_cons.
    apply: arity_spine_u_Prod_rcons; eauto.
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

Lemma s_Ind_spine_invX Gamma A B Cs ms s :
  pure Gamma ->
  arity s A ->
  [ Gamma |- spine (Ind A Cs s) ms :- B ] ->
  exists A' s t l,
    arity t A' /\
    [ Gamma |- A' :- s @ l ] /\
    arity_spine Gamma A ms A' /\
    A' <: B.
Proof.
  move=> p a ty.
  rewrite spine_spine'_rev in ty.
  apply s_Ind_spine'_invX in ty; eauto.
  rewrite revK in ty; eauto.
Qed.

Lemma s_Ind_spine_inv Gamma A Cs ms s t l :
  pure Gamma ->
  arity s A ->
  [ Gamma |- spine (Ind A Cs s) ms :- t @ l ] ->
  exists s l, arity_spine Gamma A ms (s @ l).
Proof.
  move=> p a ty.
  move: (s_Ind_spine_invX p a ty)=>[A'[s'[t'[l'[a'[tyA'[sp sb]]]]]]].
  inv a'.
  exists t'. exists l0. eauto.
  exfalso. solve_sub.
Qed.

Lemma s_Ind_spine' Gamma A B Cs s ms :
  pure Gamma ->
  [ Gamma |- spine' (Ind A Cs s) ms :- B ] ->
  [ Gamma |- Ind A Cs s :- A ].
Proof.
  move e:(spine' (Ind A Cs s) ms)=> n p ty.
  elim: ty A Cs s ms p e=>//{Gamma B n}; intros; 
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

Lemma s_Ind_spine Gamma A B Cs s ms :
  pure Gamma ->
  [ Gamma |- spine (Ind A Cs s) ms :- B ] ->
  [ Gamma |- Ind A Cs s :- A ].
Proof.
  rewrite spine_spine'_rev=> p ty.
  by move: (s_Ind_spine' p ty).
Qed.