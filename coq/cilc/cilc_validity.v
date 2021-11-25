From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion cilc_arity_spine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma merge_context_ok_inv Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- ] ->
  [ Gamma1 |- ] /\ [ Gamma2 |- ].
Proof.
  elim=>{Gamma1 Gamma2 Gamma}//=.
  move=> Gamma1 Gamma2 Gamma m mg ih h. inv h.
    move: (ih H1)=>{H1 ih}[h1 h2].
    move: (merge_re_re mg)=>[e1 e2].
    split.
    apply: u_ok; eauto. rewrite e1; eauto.
    apply: u_ok; eauto. rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma m mg ih h. inv h.
    move: (ih H1)=>{H1 ih}[h1 h2].
    move: (merge_re_re mg)=>[e1 e2].
    split.
    apply: l_ok; eauto. rewrite e1; eauto.
    apply: n_ok; eauto.
  move=> Gamma1 Gamma2 Gamma m mg ih h. inv h.
    move: (ih H1)=>{H1 ih}[h1 h2].
    move: (merge_re_re mg)=>[e1 e2].
    split.
    apply: n_ok; eauto.
    apply: l_ok; eauto. rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma mg ih h. inv h.
    move: (ih H0)=>{H0 ih}[h1 h2].
    repeat constructor; eauto.
Qed.

Theorem validity Gamma m A :
  [ Gamma |- ] ->
  [ Gamma |- m :- A ] ->
  exists s l, [ re Gamma |- A :- Sort s l ].
Proof.
  move=> wf ty. move: Gamma m A ty wf.
  apply: has_type_nested_ind=>//=; eauto.
  { move=> Gamma _ l p wf.
    exists U. exists (l.+2).
    constructor.
    rewrite <- pure_re; eauto. }
  { move=> Gamma _ _ _ l p _ _ _ _ wf.
    exists U. exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto. }
  { move=> Gamma _ _ _ l p _ _ _ _ wf.
    exists U. exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto. }
  { move=> Gamma x A h wf.
    exists U. apply: hasU_ok; eauto. }
  { move=> Gamma x A h wf.
    exists L. apply: hasL_ok; eauto. }
  { move=> Gamma n A B s t l p tyProd _ _ _ _.
    exists t. exists l.
    rewrite <- pure_re; eauto. }
  { move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf.
    move: (merge_pure2 mg p)=>->.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /u_Prod_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionU; eauto.
    replace Gamma2 with (re Gamma1).
    apply: merge_re_re_re.
    move: (pure_re p)=>->.
    rewrite e1 e2; eauto. }
  { move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /l_Prod_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionN; eauto.
    rewrite <- e1; eauto. }
  { move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf.
    move: (merge_pure2 mg p)=>->.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /u_Lolli_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionU; eauto.
    replace Gamma2 with (re Gamma1).
    apply: merge_re_re_re.
    move: (pure_re p)=>->.
    rewrite e1 e2; eauto. }
  { move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /l_Lolli_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionN; eauto.
    rewrite <- e1; eauto. }
  { move=> Gamma A s Cs l a c p tyA ihA tyCs ihCs wf.
    exists U. exists l.
    rewrite <- pure_re; eauto. }
  { move=> Gamma A s i C Cs ig p tyInd ihInd wf.
    move: (s_Ind_inv tyInd)=>[l'[_[c[_[tyA tyCs]]]]].
    exists U. exists l'.
    move: (iget_Forall ig tyCs)=>tyC.
    replace (Sort U l') with (Sort U l').[Ind A Cs s/] by autosubst.
    apply: substitutionU; eauto.
    rewrite <- pure_re; eauto.
    apply: merge_pure; eauto. }
  { move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms a mg 
    tyM ihM tyQ _ _ _ wf.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: wf1=>/ihM{ihM}[s1[l1 tyInd]].
    have p : pure (re Gamma1) by apply: re_pure.
    move: (merge_re_re mg)=>[e1 e2].
    apply s_Ind_spine_inv in tyInd; eauto.
    move: tyInd=>[sx[lx sp]].
    move: (@arity1_spine (re Gamma1) ms A sx s s' lx sp a p)=>{}sp.
    rewrite e2 in tyQ. rewrite <- e1 in tyQ.
    move: (merge_re_re_re Gamma1)=>mg1.
    move: (App_arity_spine tyQ sp mg1)=>tySp.
    exists s'. exists lx. rewrite <-e1; eauto. }
  { move=> Gamma1 Gamma2 Gamma A Q s Fs Cs m ms _ p mg 
    tyM ihM tyQ _ _ _ wf.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: wf1=>/ihM{ihM}[s1[l1 tySpInd]].
    have pr : pure (re Gamma1) by apply: re_pure.
    move: (merge_re_re mg)=>[e1 e2].
    move: (s_Ind_spine pr tySpInd)=>tyInd.
    move: (s_Ind_inv tyInd)=>[l[a[_[_[tyA _]]]]].
    apply s_Ind_spine_inv in tySpInd; eauto.
    move: tySpInd=>[sx[lx sp]].
    move: (@arity2_spine (re Gamma1) ms 
      (Ind A Cs U) A sx s lx sp a pr tyInd)=>{}sp.
    rewrite e2 in tyQ. rewrite <- e1 in tyQ.
    move: (merge_re_re_re Gamma1)=>mg1.
    move: (App_arity_spine tyQ sp mg1)=>tySp.
    exists s. exists lx.
    replace (s @ lx) with (s @ lx).[m/] by autosubst.
    apply: u_Prod_App; eauto.
    rewrite <- pure_re; eauto.
    rewrite e1. apply: merge_re_re_re. }
  { move=> Gamma A m l p tyA ihA tyM ihM wf.
    exists U. exists l.
    rewrite <- pure_re; eauto. }
Qed.