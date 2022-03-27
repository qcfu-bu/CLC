From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion cilc_arity_spine
  cilc_validity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive typing_spine : 
  context term -> term -> list term -> term -> Prop :=
| typing_spine_nil Γ A B s l :
  pure Γ ->
  A <: B ->
  [ Γ |- B :- Sort s l ] ->
  typing_spine Γ A nil B
| typing_spine_u_Arrow_cons Γ1 Γ2 Γ hd tl T A B B' l :
  pure Γ1 ->
  T <: Arrow A B U ->
  [ Γ1 |- Arrow A B U :- Sort U l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ2 B.[hd/] tl B' ->
  typing_spine Γ T (hd :: tl) B'
| typing_spine_l_Arrow_cons Γ1 Γ2 Γ hd tl T A B B' l :
  T <: Arrow A B L ->
  [ re Γ1 |- Arrow A B L :- Sort U l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ2 B.[hd/] tl B' ->
  typing_spine Γ T (hd :: tl) B'
| typing_spine_u_Lolli_cons Γ1 Γ2 Γ hd tl T A B B' l :
  pure Γ1 ->
  T <: Lolli A B U ->
  [ Γ1 |- Lolli A B U :- Sort L l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ2 B.[hd/] tl B' ->
  typing_spine Γ T (hd :: tl) B'
| typing_spine_l_Lolli_cons Γ1 Γ2 Γ hd tl T A B B' l :
  T <: Lolli A B L ->
  [ re Γ1 |- Lolli A B L :- Sort L l ] ->
  [ Γ1 |- hd :- A ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ2 B.[hd/] tl B' ->
  typing_spine Γ T (hd :: tl) B'.

Lemma arity_typing_spine Γ A ms B :
  arity_spine Γ A ms B -> typing_spine Γ A ms B.
Proof.
  move=>a. elim: a=>{Γ A ms B}.
  move=> Γ A s l p tyA.
    apply: typing_spine_nil; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l p tyArrow tyHd mg a tySp.
    apply: typing_spine_u_Arrow_cons; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l tyArrow tyHd mg a tySp.
    apply: typing_spine_l_Arrow_cons; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l p tyLolli tyHd mg a tySp.
    apply: typing_spine_u_Lolli_cons; eauto.
  move=> Γ1 Γ2 Γ hd tl A B B' l tyArrow tyHd mg a tySp.
    apply: typing_spine_l_Lolli_cons; eauto.
Qed.

Lemma App_typing_spine Γ1 Γ2 Γ m ms A B :
  [ Γ1 |- m :- A ] ->
  typing_spine Γ2 A ms B ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- spine m ms :- B ].
Proof.
  move=> tyM tsp. elim: tsp Γ1 Γ m tyM=>//={Γ2 A ms B}.
  { move=> Γ2 A B s l p sb tyA Γ1 Γ m tyM mg.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_pure2 mg p)=>->.
    apply: s_Conv; eauto.
    rewrite e1. rewrite<-e2. 
    rewrite<-pure_re; eauto. }
  { move=> Γ1 Γ2 Γ hd tl T A B B' l p sb
    tyArrow tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Arrow_App; eauto.
    apply: s_Conv; eauto.
    rewrite e1'. rewrite<-e2'.
    rewrite<-e1. rewrite<-pure_re; eauto.
    move: (merge_re2 Γ1').
    rewrite e1'.
    rewrite <-e2'.
    rewrite <-e1.
    rewrite <-pure_re; eauto. }
  { move=> Γ1 Γ2 Γ hd tl T A B B' l sb
    tyArrow tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[ΓX[mg1 mg2]].
    move: (merge_re_re mg1)=>[e1 e2].
    apply: ih; eauto.
    apply: l_Arrow_App; eauto.
    apply: s_Conv.
    apply: sb.
    2:{ apply: tyM. }
    rewrite e2. rewrite<-e1; eauto.
    apply: merge_sym; eauto. }
  { move=> Γ1 Γ2 Γ hd tl T A B B' l p sb
    tyLolli tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Lolli_App; eauto.
    apply: s_Conv; eauto.
    rewrite e1'. rewrite<-e2'.
    rewrite<-e1. rewrite<-pure_re; eauto.
    move: (merge_re2 Γ1').
    rewrite e1'.
    rewrite <-e2'.
    rewrite <-e1.
    rewrite <-pure_re; eauto. }
  { move=> Γ1 Γ2 Γ hd tl T A B B' l  sb
    tyLolli tyHd mg tySp ih Γ1' Γ2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[ΓX[mg1 mg2]].
    move: (merge_re_re mg1)=>[e1 e2].
    apply: ih; eauto.
    apply: l_Lolli_App; eauto.
    apply: s_Conv.
    apply: sb.
    2:{ apply: tyM. }
    rewrite e2. rewrite<-e1; eauto.
    apply: merge_sym; eauto. }
Qed.

Lemma typing_spine_u_Arrow_rcons Γ1 Γ2 Γ A B C n ms :
  typing_spine Γ1 A ms (Arrow B C U) ->
  pure Γ2 ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Arrow B C U)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  { rewrite /rcons.
    move: (u_Arrow_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H4 H)=>e1.
    move: (merge_pure2 H4 H2)=>e2.
    destruct s.
    { apply: typing_spine_u_Arrow_cons; eauto.
      rewrite<-e1. rewrite e2; eauto.
      apply: merge_sym; eauto.
      move: (substitutionU tyC H3 H2 H4)=>//=tyCN.
      apply: typing_spine_nil; eauto.
      rewrite<-e2; eauto. }
    { exfalso. apply: sub_Sort_False1; eauto. } }
  { move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Arrow_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto. }
Qed.

Lemma typing_spine_l_Arrow_rcons Γ1 Γ2 Γ A B C n ms :
  typing_spine Γ1 A ms (Arrow B C L) ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Arrow B C L)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  { rewrite /rcons.
    move: (l_Arrow_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H3)=>[e1 e2].
    destruct s.
    { apply: typing_spine_l_Arrow_cons.
      3:{ apply: H2. }
      apply: H0.
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H2)=>//=tyCN.
      apply: typing_spine_nil; eauto. }
    { exfalso. apply: sub_Sort_False1; eauto. } }
  { move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_u_Arrow_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto. }
Qed.

Lemma typing_spine_u_Lolli_rcons Γ1 Γ2 Γ A B C n ms :
  typing_spine Γ1 A ms (Lolli B C U) ->
  pure Γ2 ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C U)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  { rewrite /rcons.
    move: (u_Lolli_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H4 H)=>e1.
    move: (merge_pure2 H4 H2)=>e2.
    destruct s.
    { exfalso. apply: sub_Sort_False2; eauto. }
    { apply: typing_spine_u_Lolli_cons; eauto.
      rewrite<-e1. rewrite e2; eauto.
      apply: merge_sym; eauto.
      move: (substitutionU tyC H3 H2 H4)=>//=tyCN.
      apply: typing_spine_nil; eauto.
      rewrite<-e2; eauto. } }
  { move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Arrow_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto. }
Qed.

Lemma typing_spine_l_Lolli_rcons Γ1 Γ2 Γ A B C n ms :
  typing_spine Γ1 A ms (Lolli B C L) ->
  [ Γ2 |- n :- B ] ->
  merge Γ1 Γ2 Γ ->
  typing_spine Γ A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C L)=> T sp.
  elim: sp Γ2 Γ B C n e=>{Γ1 A ms T}; intros; subst.
  { rewrite /rcons.
    move: (l_Lolli_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H3)=>[e1 e2].
    destruct s.
    { exfalso. apply: sub_Sort_False2; eauto. }
    { apply: typing_spine_l_Lolli_cons.
      3:{ apply: H2. }
      apply: H0.
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H2)=>//=tyCN.
      apply: typing_spine_nil; eauto. } }
  { move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_u_Arrow_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Arrow_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Γ4[mg1 mg2]].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto. }
  { move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Γ4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto. }
Qed.

Lemma typing_spine_strengthen Γ A B C ms s l :
  typing_spine Γ B ms C ->
  A <: B ->
  [ re Γ |- B :- s @ l ] ->
  typing_spine Γ A ms C.
Proof.
  move=>sp. elim: sp A s l=>{Γ B C ms}.
  move=> Γ A B s l p sb tyB C s' l' sb' tyC.
    apply: typing_spine_nil; eauto.
    apply: sub_trans; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l p sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_u_Arrow_cons; eauto.
    apply: sub_trans; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_l_Arrow_cons; eauto.
    apply: sub_trans; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l p sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: sub_trans; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma typing_spine_weaken Γ A B C ms s l :
  typing_spine Γ A ms B ->
  B <: C ->
  [ re Γ |- C :- s @ l ] ->
  typing_spine Γ A ms C.
Proof.
  move=>sp. elim: sp C s l=>{Γ A B ms}.
  move=> Γ A B s l p sb tyB C s' l' sb' tyC.
    apply: typing_spine_nil; eauto.
    apply: sub_trans; eauto.
    rewrite <-pure_re in tyC; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l p sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_u_Arrow_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_l_Arrow_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l p sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
  move=> Γ1 Γ2 Γ hd tl T A B B' l sb
    tyArrow tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
Qed.

Lemma spine'_inv Γ m ms B :
  [ Γ |- ] ->
  [ Γ |- spine' m ms :- B ] ->
  exists Γ1 Γ2 A,
    merge Γ1 Γ2 Γ /\
    [ Γ1 |- m :- A ] /\
    typing_spine Γ2 A (rev ms) B.
Proof.
  move e:(spine' m ms)=> n wf ty.
  elim: ty m ms wf e=>{Γ n B}.
  { move=> Γ s l p m ms wf sp. 
    destruct ms; try discriminate. simpl in sp; subst.
    exists Γ. exists Γ. exists (U @ l.+1).
    rewrite /rev/catrev.
    repeat constructor; eauto.
    apply: merge_pure; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto. }
  { move=> Γ A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Γ. exists Γ. exists (U @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: u_Arrow; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto. }
  { move=> Γ A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Γ. exists Γ. exists (U @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: l_Arrow; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto. }
  { move=> Γ A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Γ. exists Γ. exists (L @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: u_Lolli; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto. }
  { move=> Γ A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Γ. exists Γ. exists (L @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: l_Lolli; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto. }
  { move=> Γ x A h m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    move: (hasU_pure h)=>p.
    move: (hasU_ok wf h)=>[l tyA].
    exists Γ. exists (re Γ). exists A.
    repeat split.
    rewrite<- !pure_re; eauto.
    apply: merge_pure; eauto.
    apply: u_Var; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure; eauto. }
  { move=> Γ x A h m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    move: (hasL_ok wf h)=>[l tyA].
    exists Γ. exists (re Γ). exists A.
    repeat split.
    apply: merge_re2.
    apply: l_Var; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure; eauto. }
  { move=> Γ n A B s t l p tyArrow ihArrow tyN ihN m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    exists Γ. exists Γ. exists (Arrow A B s).
    repeat split.
    apply: merge_pure; eauto.
    apply: u_Lam; eauto.
    apply: typing_spine_nil; eauto. }
  { move=> Γ n A B s t l tyLolli ihLolli tyN ihN m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    exists Γ. exists (re Γ). exists (Lolli A B s).
    repeat split.
    apply: merge_re2.
    apply: l_Lam; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure. }
  { move=> Γ1 Γ2 Γ A B m n p tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    { subst.
      move: (merge_pure2 mg p)=>e; subst.
      move: (merge_re_re mg)=>[e1 e2].
      move: (u_Arrow_App p tyM tyN mg)=>tyApp.
      move: (validity wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Γ1. exists Γ2. exists (B.[n/]).
      repeat split; eauto.
      apply: typing_spine_nil; eauto.
      replace Γ2 with (re Γ2).
      rewrite e2; eauto.
      rewrite<-pure_re; eauto. }
    { inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Γ3[Γ4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Γ5[mg1 mg2]].
      move: (merge_pure2 mg1 p)=>{}e.
      exists Γ3. exists Γ5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_u_Arrow_rcons; eauto. } }
  { move=> Γ1 Γ2 Γ A B m n tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    { subst.
      move: (l_Arrow_App tyM tyN mg)=>tyApp.
      move: (validity wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Γ. exists (re Γ). exists (B.[n/]).
      repeat split; eauto.
      apply: merge_re2.
      apply: typing_spine_nil; eauto.
      apply: re_pure. }
    { inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Γ3[Γ4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Γ5[mg1 mg2]].
      exists Γ3. exists Γ5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_l_Arrow_rcons; eauto. } } 
  { move=> Γ1 Γ2 Γ A B m n p tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    { subst.
      move: (merge_pure2 mg p)=>e; subst.
      move: (merge_re_re mg)=>[e1 e2].
      move: (u_Lolli_App p tyM tyN mg)=>tyApp.
      move: (validity wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Γ1. exists Γ2. exists (B.[n/]).
      repeat split; eauto.
      apply: typing_spine_nil; eauto.
      replace Γ2 with (re Γ2).
      rewrite e2; eauto.
      rewrite<-pure_re; eauto. }
    { inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Γ3[Γ4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Γ5[mg1 mg2]].
      move: (merge_pure2 mg1 p)=>{}e.
      exists Γ3. exists Γ5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_u_Lolli_rcons; eauto. } }
  { move=> Γ1 Γ2 Γ A B m n tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    { subst.
      move: (l_Lolli_App tyM tyN mg)=>tyApp.
      move: (validity wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Γ. exists (re Γ). exists (B.[n/]).
      repeat split; eauto.
      apply: merge_re2.
      apply: typing_spine_nil; eauto.
      apply: re_pure. }
    { inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Γ3[Γ4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Γ5[mg1 mg2]].
      exists Γ3. exists Γ5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_l_Lolli_rcons; eauto. } }
  { move=> Γ A Cs s t l a cs p tyA ihA tyCs m ms wf sp.
    destruct ms; simpl in sp; try discriminate; subst.
    rewrite /rev/catrev.
    exists Γ. exists Γ. exists A.
    repeat split.
    apply: merge_pure; eauto.
    apply: s_Ind; eauto.
    apply: typing_spine_nil; eauto. }
  { move=> Γ A s i C Cs I ig p tyI ihI m ms wf sp.
    destruct ms; simpl in sp; try discriminate; subst.
    move: (s_Ind_inv tyI)=>[t[l[a[cs[_[tyA tyCs]]]]]].
    move: (iget_Forall ig tyCs)=>tyC.
    have mg : merge Γ Γ Γ.
      apply: merge_pure; eauto.
    move: (substitutionU tyC tyI p mg)=>tyCI.
    rewrite /rev/catrev.
    exists Γ. exists Γ. exists (C.[I/]).
    repeat split.
    apply: merge_pure; eauto.
    apply: s_Constr; eauto.
    apply: typing_spine_nil; eauto. }
  { move=> Γ1 Γ2 Γ A Q s s' Fs Cs m ms I a mg
    tyM ihM tyQ ihQ tyFsCs m0 ms0 wf sp.
    destruct ms0; simpl in sp; try discriminate; subst.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].
    have mg' : merge (re Γ2) (re Γ1) (re Γ).
      rewrite e1. rewrite e2. apply: merge_re_re_re.
    move: (validity wf1 tyM)=>[s0[l tyI]].
    have p : pure (re Γ1).
      apply: re_pure.
    move: (s_Ind_spine_inv p a tyI)=>[s1[l0 tySp]].
    move: (arity1_spine s' tySp a p)=>{tySp}/arity_typing_spine tySp.
    move: (App_typing_spine tyQ tySp mg')=>{}tySp.
    rewrite /rev/catrev.
    exists Γ. exists (re Γ). exists (spine Q ms).
    repeat split; eauto.
    apply: merge_re2.
    apply: s_Case; eauto.
    apply: typing_spine_nil.
    apply: re_pure.
    eauto.
    apply: tySp. }
  { move=> Γ1 Γ2 Γ A Q s Fs Cs m ms I a p mg
    tyM ihM tyQ ihQ tyFsCs m0 ms0 wf sp.
    destruct ms0; simpl in sp; try discriminate; subst.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].      
    have mg' : merge (re Γ2) (re Γ1) (re Γ).
      rewrite e1. rewrite e2. apply: merge_re_re_re.    
    have tyM' : [ re Γ1 |- m :- spine I ms ].
      rewrite <-pure_re; eauto.
    move: (validity wf1 tyM)=>[s0[l tyI]].
    have pr : pure (re Γ1).
      apply: re_pure.
    move: (s_Ind_spine pr tyI)=>tyInd.
    move: (s_Ind_inv tyInd)=>{a}[t[l0[a[cs[_[tyA tyCs]]]]]].
    move: (s_Ind_spine_inv pr a tyI)=>[s1[l1 tySp]].
    move: (arity2_spine s tySp a pr tyInd)=>{tySp}/arity_typing_spine tySp.
    move: (App_typing_spine tyQ tySp mg')=>{}tySp.
    rewrite <-e2 in tySp.
    move: (u_Arrow_App pr tySp tyM' mg')=>tyApp.
    rewrite /rev/catrev.
    exists Γ. exists (re Γ). exists (App (spine Q ms) m).
    repeat split; eauto.
    apply: merge_re2.
    apply: s_DCase; eauto.
    rewrite <-pure_re; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure. }
  { move=> Γ A m l p tyA ihA tyM ihM m0 ms wf sp.
    destruct ms; simpl in sp; try discriminate; subst.
    exists Γ. exists Γ. exists A.
    repeat split.
    apply: merge_pure; eauto.
    eapply u_Fix; eauto.
    apply: typing_spine_nil; eauto. }
  { move=> Γ A B m s l sb tyB ihB tyM ihM m0 ms wf sp.
    subst.
    have e : (spine' m0 ms = spine' m0 ms) by eauto.
    move: (ihM m0 ms wf e)=>[Γ1[Γ2[A0[mg[tyM0 tySp]]]]].
    move: (merge_re_re mg)=>[e1 e2].
    exists Γ1. exists Γ2. exists A0.
    repeat split; eauto.
    apply: typing_spine_weaken; eauto.
    rewrite e2; eauto. }
Qed.

Lemma spine_inv Γ m ms B :
  [ Γ |- ] ->
  [ Γ |- spine m ms :- B ] ->
  exists Γ1 Γ2 A,
    merge Γ1 Γ2 Γ /\
    [ Γ1 |- m :- A ] /\
    typing_spine Γ2 A ms B.
Proof.
  rewrite spine_spine'_rev=>wf tySp.
  move: (spine'_inv wf tySp)=>[Γ1[Γ2[A[mg[tyM sp]]]]].
  rewrite revK in sp.
  exists Γ1. 
  exists Γ2.
  exists A.
  eauto.
Qed.