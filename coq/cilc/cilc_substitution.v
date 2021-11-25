From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ Δ |- σ -| Γ ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil σ :
  [ nil |- σ -| nil ]
| agree_subst_u Δ σ Γ A :
  [ Δ |- σ -| Γ ] ->
  [ A.[σ] +u Δ |- up σ -| A +u Γ ]
| agree_subst_l Δ σ Γ A :
  [ Δ |- σ -| Γ ] ->
  [ A.[σ] +l Δ |- up σ -| A +l Γ ]
| agree_subst_n Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  [ +n Δ |- up σ -| +n Γ ]
| agree_subst_wkU Δ σ Γ n A :
  [ Δ |- σ -| Γ ] ->
  [ re Δ |- n :- A.[σ] ] ->
  [ Δ |- n .: σ -| A +u Γ ]
| agree_subst_wkL Δ1 Δ2 Δ σ Γ n A :
  merge Δ1 Δ2 Δ ->
  [ Δ1 |- σ -| Γ ] ->
  [ Δ2 |- n :- A.[σ] ] ->
  [ Δ |- n .: σ -| A +l Γ ]
| agree_subst_wkN Δ σ Γ n :
  [ Δ |- σ -| Γ ] ->
  [ Δ |- n .: σ -| +n Γ ]
| agree_subst_convU Δ σ Γ A B l :
  A <: B ->
  [ re Δ |- B.[ren (+1)].[σ] :- Sort U l ] ->
  [ Δ |- σ -| A +u Γ ] ->
  [ Δ |- σ -| B +u Γ ]
| agree_subst_convL Δ σ Γ A B l :
  A <: B ->
  [ re Δ |- B.[ren (+1)].[σ] :- Sort L l ] ->
  [ re Γ |- B :- Sort L l ] ->
  [ Δ |- σ -| A +l Γ ] ->
  [ Δ |- σ -| B +l Γ ]
where "[ Δ |- σ -| Γ ]" := (agree_subst Δ σ Γ).

Lemma agree_subst_pure Δ σ Γ :
  [ Δ |- σ -| Γ ] -> pure Γ -> pure Δ.
Proof with eauto using pure.
  elim=>//=...
  move=> Δ' σ' Γ' A ag h p. inv p...
  move=> Δ' σ' Γ' A ag h p. inv p.
  move=> Δ' σ' Γ' ag h p. inv p...
  move=> Δ' σ' Γ' n A ag1 h ag2 p. inv p...
  move=> Δ1 Δ2 Δ' σ' Γ' n A mg ag1 h ag2 p. inv p.
  move=> Δ' σ' Γ' _ ag h p. inv p...
  move=> Δ' σ' Γ' A B l sb ag1 ag2 h p. inv p...
  move=> Δ' σ' Γ' A B l sb ty1 ty2 ag h p. inv p.
Qed.

Lemma agree_subst_refl Γ : [ Γ |- ids -| Γ ].
Proof with eauto using agree_subst.
  elim: Γ...
  move=> a Γ ag.
  destruct a.
  destruct p.
  destruct s.
  replace [ t +u Γ |- ids -| t +u Γ ]
    with [ t.[ids] +u Γ |- up ids -| t +u Γ ]
    by autosubst...
  replace [ t +l Γ |- ids -| t +l Γ ]
    with [ t.[ids] +l Γ |- up ids -| t +l Γ ]
    by autosubst...
  replace ids with (up ids) by autosubst...
Qed.

Lemma agree_subst_hasU Δ σ Γ x A :
  [ Δ |- σ -| Γ ] ->
  hasU Γ x A ->
  [ Δ |- σ x :- A.[σ] ].
Proof.
  move=> ag. elim: ag x A=>{σ Δ Γ}.
  move=> σ x A h. inv h.
  move=> Δ σ Γ A ag ih x A' h. inv h; asimpl.
    apply: u_Var.
    replace (A.[σ >> ren (+1)])
      with (A.[σ].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_subst_pure; eauto.
    apply: eweakeningU; eauto. autosubst.
  move=> Δ σ Γ A ag ih x A' h. inv h.
  move=> Δ σ Γ Ag ih x A h. inv h.
    apply: eweakeningN; eauto; autosubst.
  move=> Δ σ Γ n A ag ih ty x A' h. 
    inv h; asimpl; eauto.
    have p := agree_subst_pure ag H3.
    by rewrite (pure_re p).
  move=> Δ1 Δ2 Δ σ Γ n A mg ag ih ty x A' h. 
    inv h.
  move=> Δ σ Γ n ag ih x A h. inv h; asimpl; eauto.
  move=> Δ σ Γ A B l sb ty ag ih x A' h. inv h.
    have h' : hasU (A +u Γ) 0 A.[ren (+1)].
      constructor; eauto.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub_ren; eauto.
    apply: ty.
    apply: ih; eauto.
    apply: ih.
    constructor; eauto.
  move=> Δ σ Γ A B l sb t1 ty2 ag ih x A' h.
    inv h.
Qed.

Lemma agree_subst_hasL Δ σ Γ x A :
  [ Δ |- σ -| Γ ] ->
  hasL Γ x A ->
  [ Δ |- σ x :- A.[σ] ].
Proof.
  move=> ag. elim: ag x A=>{Δ σ Γ}.
  move=> σ x A h. inv h.
  move=> Δ σ Γ A ag ih x A' h. inv h.
    apply: eweakeningU; eauto; autosubst.
  move=> Δ σ Γ A ag ih x A' h. inv h; asimpl.  
    replace (A.[σ >> ren (+1)])
      with (A.[σ].[ren (+1)]) by autosubst.
    apply: l_Var.
    constructor.
    apply: agree_subst_pure; eauto.
  move=> Δ σ Γ ag ih x A h. inv h.
    apply: eweakeningN; eauto; autosubst.
  move=> Δ σ Γ n A ag ih ty x A' h. 
    inv h; asimpl; eauto.
  move=> Δ1 Δ2 Δ σ Γ n A mg ag ih ty x A' h.
    inv h; asimpl.
    have p := agree_subst_pure ag H3.
    rewrite (merge_pure1 mg p); eauto.
  move=> Δ σ Γ n ag ih x A h. inv h; asimpl; eauto.
  move=> Δ σ Γ A B l sb ty ag ih x A' h. inv h.
    apply: ih.
    constructor; eauto.
  move=> Δ σ Γ A B l sb ty1 ty2 ag ih x A' h. inv h.
    have h' : hasL (A +l Γ) 0 A.[ren (+1)].
      constructor; eauto.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub_ren; eauto.
    apply: ty1.
    apply: ih; eauto.
Qed.

Lemma agree_subst_re_re Δ σ Γ :
  [ Δ |- σ -| Γ ] ->
  [ re Δ |- σ -| re Γ ].
Proof with eauto using agree_subst.
  move=> ag. elim: ag=>//={Δ σ Γ}...
  move=> Δ σ Γ n A ag1 ag2 ty.
    constructor...
    rewrite <- re_re...
  move=> Δ1 Δ2 Δ σ Γ n A mg ag1 ag2 ty.
    constructor...
    move: (merge_re_re mg)=>[<-_]...
  move=> Δ σ Γ A B l sb ty ag1 ag2.
    apply: agree_subst_convU...
    rewrite <- re_re...
Qed.

Lemma merge_agree_subst_inv Δ σ Γ1 Γ2 Γ :
  [ Δ |- σ -| Γ ] ->
  merge Γ1 Γ2 Γ ->
  exists Δ1 Δ2,
    merge Δ1 Δ2 Δ /\
    [ Δ1 |- σ -| Γ1 ] /\
    [ Δ2 |- σ -| Γ2 ].
Proof.
  move=> ag. elim: ag Γ1 Γ2=>{Δ σ Γ}.
  move=> σ Γ1 Γ2 mg. inv mg.
    exists nil. exists nil. repeat constructor; eauto.
  move=> Δ σ Γ A ag ih Γ1 Γ2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Δ1[Δ2[mg'[ag1 ag2]]]].
    exists (A.[σ] +u Δ1).
    exists (A.[σ] +u Δ2).
    repeat constructor; eauto.
  move=> Δ σ Γ A ag ih Γ1 Γ2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Δ1[Δ2[mg'[ag1 ag2]]]].
      exists (A.[σ] +l Δ1).
      exists (+n Δ2).
      repeat constructor; eauto.
    move: (ih _ _ H2)=> {H2}[Δ1[Δ2[mg'[ag1 ag2]]]].
      exists (+n Δ1).
      exists (A.[σ] +l Δ2).
      repeat constructor; eauto.
  move=> Δ σ Γ ag ih Γ1 Γ2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Δ1[Δ2[mg'[ag1 ag2]]]].
    exists (+n Δ1).
    exists (+n Δ2).
    repeat constructor; eauto.
  move=> Δ σ Γ n A ag ih ty Γ1 Γ2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Δ1[Δ2[mg'[ag1 ag2]]]].
    exists Δ1. 
    exists Δ2.
    move: (merge_re_re mg')=>[e1 e2]. 
    repeat constructor; eauto.
    move: e1=>->; eauto.
    move: e2=>->; eauto.
  move=> Δ1 Δ2 Δ σ Γ n A mg1 ag ih ty
    Γ1 Γ2 mg2. inv mg2.
    move: (ih _ _ H2)=> {H2}[Δ1'[Δ2'[mg'[ag1 ag2]]]].
      move: (merge_split1 mg1 mg')=>[Δ'[mg1' mg2']].
      exists Δ'. 
      exists Δ2'.
      repeat constructor; eauto.
      apply: agree_subst_wkL; eauto.
    move: (ih _ _ H2)=> {H2}[Δ1'[Δ2'[mg'[ag1 ag2]]]].
      move: (merge_split2 mg1 mg')=>[Δ'[mg1' mg2']].
      exists Δ1'.
      exists Δ'.
      repeat constructor; eauto.
      apply: agree_subst_wkL; eauto.
  move=> Δ σ Γ n ag ih Γ1 Γ2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Δ1[Δ2[mg'[ag1 ag2]]]].
    exists Δ1.
    exists Δ2.
    repeat constructor; eauto.
  move=> Δ σ Γ A B l sb ty ag ih Γ1 Γ2 mg.
    inv mg.
    have mg : merge (A +u Γ0) (A +u Γ3) (A +u Γ).
      constructor; eauto.
    move: (ih _ _ mg)=>{mg}[Δ1[Δ2[mg[ag1 ag2]]]].
    exists Δ1.
    exists Δ2.
    move: (merge_re_re mg)=>[e1 e2].
    repeat constructor; eauto.
    apply: agree_subst_convU; eauto.
    rewrite e1; eauto.
    apply: agree_subst_convU; eauto.
    rewrite e2; eauto.
  move=> Δ σ Γ A B l sb ty1 ty2 ag ih Γ1 Γ2 mg.
    inv mg.
    have mg' : merge (A +l Γ0) (+n Γ3) (A +l Γ).
      constructor; eauto.
      move: (ih _ _ mg')=>{mg'}[Δ1[Δ2[mg'[ag1 ag2]]]].
      exists Δ1.
      exists Δ2.
      move: (merge_re_re H2)=>[eG1 eG2].
      move: (merge_re_re mg')=>[eD1 eD2].
      repeat constructor; eauto.
      apply: agree_subst_convL; eauto.
      move: eD1=>->; eauto.
      move: eG1=>->; eauto.
    have mg' : merge (+n Γ0) (A +l Γ3) (A +l Γ).
      constructor; eauto.
      move: (ih _ _ mg')=>{mg'}[Δ1[Δ2[mg'[ag1 ag2]]]].
      exists Δ1.
      exists Δ2.
      move: (merge_re_re H2)=>[eG1 eG2].
      move: (merge_re_re mg')=>[eD1 eD2].
      repeat constructor; eauto.
      apply: agree_subst_convL; eauto.
      move: eD2=>->; eauto.
      move: eG2=>->; eauto.
Qed.

Lemma arity_subst s A σ :
  arity s A -> arity s A.[σ].
Proof with eauto using arity.
  move=> ar. elim: ar σ...
Qed.

Definition n_subst σ x := 
  (forall i, ~x = i -> noccurs x (σ i)) /\ σ x = Var x.

Lemma noccurs_ren0 x m ξ :
  (forall i, ~ξ i = x) -> noccurs x m.[ren ξ].
Proof with eauto using noccurs, List.Forall.
  move: m x ξ. apply: term_ind_nested...
  move=> A B s ihA ihB x ξ h; asimpl.
    constructor...
    apply: ihB=> i.
    destruct i; asimpl; eauto.
  move=> A B s ihA ihB x ξ h; asimpl.
    constructor...
    apply: ihB=> i.
    destruct i; asimpl; eauto.
  move=> A m s ihA ihM x ξ h; asimpl.
    constructor...
    apply: ihM=> i.
    destruct i; asimpl; eauto.
  move=> A Cs s ihA ihCs x ξ h; asimpl.
    constructor...
    elim: ihCs...
    move=> C Cs' hd tl ih.
    constructor...
    apply: hd=> i.
    destruct i; asimpl; eauto.
  move=> m Q Fs ihM ihQ ihFs x ξ h; asimpl.
    constructor...
    elim: ihFs...
  move=> m Q Fs ihM ihQ ihFs x ξ h; asimpl.
    constructor...
    elim: ihFs...
  move=> A m ihA ihM x ξ h; asimpl.
    constructor...
    apply: ihM=> i.
    destruct i; asimpl; eauto.
Qed.

Lemma n_subst0 σ : n_subst (up σ) 0.
Proof.
  split; eauto.
  move=> i. elim: i σ=>//=.
  move=> i _ σ _; asimpl.
  apply: noccurs_ren0; eauto.
Qed.

Lemma noccurs_up x m ξ :
  noccurs x m -> 
    (forall i, ~x = i -> ~ξ x = ξ i) -> 
    noccurs (ξ x) m.[ren ξ].
Proof with eauto using noccurs.
  move=> no. move: x m no ξ.
  apply: noccurs_ind_nested=>//=... 
  move=> x A B s noA ihA noB ihB ξ h.
    constructor; asimpl; eauto.
    apply: ihB=> i. 
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A B s noA ihA noB ihB ξ h.
    constructor; asimpl; eauto.
    apply: ihB=> i. 
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A m s noA ihA noM ihM ξ h.
    constructor; asimpl; eauto.
    apply: ihM=> i.
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A Cs s noA ihA noCs ihCs ξ h.
    constructor; asimpl; eauto.
    elim: ihCs.
    asimpl; constructor.
    move=> C Cs' hd tl ih; asimpl.
    constructor; eauto.
    apply: hd=> i neq.
    destruct i; asimpl; eauto.
    have /h neq' : ~x = i by eauto.
    eauto.
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs ξ h.
    constructor; asimpl; eauto.
    elim: ihFs.
    asimpl; constructor.
    move=> F Fs' hd tl ih; asimpl.
    constructor; eauto.
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs ξ h.
    constructor; asimpl; eauto.
    elim: ihFs.
    asimpl; constructor.
    move=> F Fs' hd tl ih; asimpl.
    constructor; eauto.
  move=> x A m noA ihA noM ihM ξ h.
    constructor; asimpl; eauto.
    apply: ihM=> i neq.
    destruct i; asimpl; eauto.
    have /h neq' : ~x = i by eauto.
    eauto.
Qed.

Lemma n_subst_up σ x :
  n_subst σ x -> n_subst (up σ) x.+1.
Proof.
  move=>[h e]. split; asimpl.
  elim; asimpl.
  constructor; eauto.
  move=> n h' neq.
  have pf : ~x = n by eauto.
  move: (h _ pf)=>{}h.
  apply: noccurs_up; eauto.
  rewrite e. autosubst.
Qed.

Lemma noccurs_subst σ m x :
  noccurs x m -> n_subst σ x -> noccurs x m.[σ].
Proof with eauto using noccurs.
  move=> no. move: x m no σ.
  apply: noccurs_ind_nested=>//=...
  move=> x y neq σ [n _]...
  move=> x A B s noA ihA noB ihB σ no.
    constructor...
    apply: ihB...
    apply: n_subst_up...
  move=> x A B s noA ihA noB ihB σ no.
    constructor...
    apply: ihB...
    apply: n_subst_up...
  move=> x A m s noA ihA noM ihM σ no.
    constructor...
    apply: ihM...
    apply: n_subst_up...
  move=> x A Cs s noA ihA noCs ihCs σ no.
    constructor...
    elim: ihCs noCs; asimpl.
    constructor.
    move=> C Cs' hd tl ih1 ih2. inv ih2.
    constructor...
    apply: hd.
    apply: n_subst_up...
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs σ no.
    constructor...
    elim: ihFs noFs; asimpl.
    constructor.
    move=> F Fs' hd tl ih1 ih2. inv ih2.
    constructor...
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs σ no.
    constructor...
    elim: ihFs noFs; asimpl.
    constructor.
    move=> F Fs' hd tl ih1 ih2. inv ih2.
    constructor...
  move=> x A m noA ihA noM ihM σ no.
    constructor...
    apply: ihM.
    apply: n_subst_up...
Qed.

Lemma pos_subst i A σ :
  pos i A -> n_subst σ i -> pos i A.[σ].
Proof with eauto.
  move=> p. elim: p σ=>//={i A}.
  move=> x ms noMs σ [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: noMs.
    constructor.
    move=> m ms' noM noMs ihMs; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B s noA pB ihB σ n.
    constructor.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B s noA pB ihB σ n.
    constructor.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
Qed.

Lemma active_subst i m σ :
  active i m -> n_subst σ i -> active i m.[σ].
Proof with eauto using List.Forall.
  move=> a. elim: a σ=>{i m}=>//=.
  move=> x ms no σ [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no...
    move=> m ms' hd tl ih; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B s p a ihB nB σ n.
    apply: active_Pos.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B s noA a ihB σ n.
    apply: active_Lolli.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
Qed.

Lemma constr_subst i s (m : term) σ :
  constr i s m -> n_subst σ i -> constr i s m.[σ].
Proof with eauto.
  move=> c. elim: c σ=>{i s m}=>//=.
  move=> x s ms no σ [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no.
    constructor.
    move=> m ms' hd tl ih; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B p cB ihB nB σ n.
    apply: constr_UPos.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B noA cB ihB σ n.
    apply: constr_UProd.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B p cB ihB nB σ n.
    apply: constr_LPos1.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B p a noB σ n.
    apply: constr_LPos2.
    apply: pos_subst...
    apply: active_subst...
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B noA cB ihB σ n.
    apply: constr_LProd1.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B noA a σ n.
    apply: constr_LProd2.
    apply: noccurs_subst...
    apply: active_subst...
    apply: n_subst_up...
Qed.

Lemma arity1_subst s s' A σ :
  arity s A -> (arity1 s' A).[σ] = arity1 s' A.[σ].
Proof.
  move=> a. elim: a σ s'=>//={A}.
  move=> A B a ih σ s'.
  rewrite ih; eauto.
Qed.

Lemma arity2_subst s s' I A σ :
  arity s A -> (arity2 s' I A).[σ] = arity2 s' I.[σ] A.[σ].
Proof.
  move=> a. elim: a I σ s'=>//={A}.
  move=> A B a ih I σ s'; asimpl.
  rewrite ih; asimpl; eauto.
Qed.

Lemma respine_I_subst Q I σ :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  Q.[σ] = respine Q.[σ] I.[σ].
Proof.
  elim: I σ Q=>//=.
  move=> x σ Q _ h.
    move: (h x)=>//=.
  move=> A _ B _ s σ Q h _.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s σ Q h _.
    move: (h (Var 0))=>//=.
  move=> m _ n _ ξ Q h _.
    move: (h (Var 0))=>//=.
Qed.

Lemma drespine_I_subst Q c I σ :
  (forall Q, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  App Q.[σ] c.[σ] = drespine Q.[σ] c.[σ] I.[σ].
Proof.
  elim: I σ Q=>//=.
  move=> x σ Q _ h.
    move: (h x)=>//=.
  move=> A _ B _ s σ Q h _.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s σ Q h _.
    move: (h (Var 0))=>//=.
  move=> m _ n _ ξ Q h _.
    move: (h (Var 0))=>//=.
Qed.

Lemma respine_spine'_I_subst Q I ms σ :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine Q (spine' I ms)).[σ] =
    respine Q.[σ] (spine' I ms).[σ].
Proof.
  elim: ms Q I σ=>//=.
  move=> Q I σ h1 h2.
    rewrite h1.
    by apply: respine_I_subst.
  move=> m ms ih Q I ξ h1 h2.
    rewrite ih; eauto.
Qed.

Lemma drespine_spine'_I_subst Q c I ms σ :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  (drespine Q c (spine' I ms)).[σ] =
    drespine Q.[σ] c.[σ] (spine' I ms).[σ].
Proof.
  elim: ms Q I σ=>//=.
  move=> Q I σ h1 h2.
    rewrite h1.
    by apply: drespine_I_subst.
  move=> m ms ih Q I ξ h1 h2.
    repeat f_equal.
    apply: respine_spine'_I_subst; eauto.
    by apply: drespine_respine.
Qed.

Lemma respine_spine_I_subst Q I ms σ :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine Q (spine I ms)).[σ] =
    respine Q.[σ] (spine I ms).[σ].
Proof.
  move=> h1 h2.
  rewrite spine_spine'_rev.
  by rewrite respine_spine'_I_subst.
Qed.

Lemma drespine_spine_I_subst Q c I ms σ :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  (drespine Q c (spine I ms)).[σ] =
    drespine Q.[σ] c.[σ] (spine I ms).[σ].
Proof.
  move=> h1 h2.
  rewrite spine_spine'_rev.
  by rewrite drespine_spine'_I_subst.
Qed.

Lemma ren_Var_False (I : var -> term) x :
  (forall y, ~I x = Var y) -> (forall y, ~(I x).[ren (+1)] = Var y).
Proof.
  move e:(I x)=> n h y.
  elim: n h I e y; intros; try discriminate.
  destruct y; asimpl.
  discriminate.
  move: (h y)=>{}h eq.
  inv eq.
  apply: h; eauto.
Qed.

Lemma active_respine_subst n (A Q C : term) Cs I σ :
  active n C ->
  I n = Ind A Cs L ->
  (forall x, ~I n = Var x) ->
  (respine Q C.[I]).[σ] =
    respine Q.[σ] C.[I].[σ].
Proof.
  move=> c.
  elim: c A Q Cs I σ; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.
    asimpl. rewrite H0; simpl; eauto.    
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H3; asimpl; eauto.
    rewrite H3; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H2; asimpl; eauto.
    rewrite H2; asimpl; discriminate.
Qed.

Lemma active_drespine_subst n (A Q c C : term) Cs I σ :
  active n C ->
  I n = Ind A Cs L ->
  (forall x, ~I n = Var x) ->
  (drespine Q c C.[I]).[σ] =
    drespine Q.[σ] c.[σ] C.[I].[σ].
Proof.
  move=> a.
  elim: a c Q I σ; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.
    asimpl. rewrite H0; simpl; eauto.    
  - asimpl. repeat f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    asimpl. rewrite H3; asimpl; eauto.
    asimpl. rewrite H3; discriminate.
  - asimpl. repeat f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    asimpl. rewrite H2; asimpl; eauto.
    asimpl. rewrite H2; discriminate.
Qed.

Lemma constr_respine_subst n (A Q C : term) Cs I σ s :
  constr n s C ->
  I n = Ind A Cs s ->
  (forall x, ~I n = Var x) ->
  (respine Q C.[I]).[σ] =
    respine Q.[σ] C.[I].[σ].
Proof.
  move=> c.
  elim: c A Q Cs I σ; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.
    asimpl.
    rewrite H0; simpl; eauto.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H3; asimpl; eauto.
    rewrite H3; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H2; asimpl; eauto.
    rewrite H2; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H3; asimpl; eauto.
    rewrite H3; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    asimpl. rewrite H2; asimpl; eauto.
    asimpl. rewrite H2; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H2; asimpl; eauto.
    rewrite H2; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    asimpl. rewrite H1; asimpl; eauto.
    asimpl. rewrite H1; asimpl; discriminate.
Qed.

Lemma constr_drespine_subst n s (A Q c C : term) Cs I σ :
  constr n s C ->
  I n = Ind A Cs s ->
  (forall x, ~I n = Var x) ->
  (drespine Q c C.[I]).[σ] =
    drespine Q.[σ] c.[σ] C.[I].[σ].
Proof.
  move=> cn.
  elim: cn A Q c Cs I σ; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.
    asimpl. rewrite H0; simpl; eauto.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H3; asimpl; eauto.
    rewrite H3; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H2; asimpl; eauto.
    rewrite H2; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H3; asimpl; eauto.
    rewrite H3; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite active_drespine_subst; asimpl; eauto.
    asimpl. rewrite H2; asimpl; eauto.
    asimpl. rewrite H2; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite H1; asimpl; eauto.
    rewrite H2; asimpl; eauto.
    rewrite H2; asimpl; discriminate.
  - asimpl. f_equal.
    erewrite active_drespine_subst; asimpl; eauto.
    asimpl. rewrite H1; asimpl; eauto.
    asimpl. rewrite H1; asimpl; discriminate.
Qed.

Lemma All2_case_subst Γ Δ s A Q Fs Cs Cs' σ :
  All2 (fun F C =>
    constr 0 s C /\
    forall Δ σ, [ Δ |- σ -| Γ ] ->
      [ Δ |- F.[σ] :- (case (Ind A Cs' s) Q C).[σ] ])
    Fs Cs ->
  [ Δ |- σ -| Γ ] ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Δ |- F :- case (Ind A.[σ] Cs'..[up σ] s) Q.[σ] C])
  Fs..[σ] Cs..[up σ].
Proof.
  elim: Fs Γ Δ s A Q Cs σ.
  move=> Γ Δ s A Q Cs σ h. inv h.
    constructor.
  move=> F Fs ih Γ Δ s A Q Cs σ h ag.
  destruct Cs; inv h. inv H2; asimpl.
  constructor. split.
  - apply: constr_subst; eauto.
    apply: n_subst0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold case in H0.
    erewrite constr_respine_subst in H0; eauto.
    asimpl in H0.
    by unfold case; asimpl.
    asimpl; eauto.
    move=> i Q'; discriminate.
  - apply: ih; eauto.
Qed.

Lemma All2i_dcase_subst Γ Δ n s A Q Fs Cs Cs' σ :
  All2i (fun i F C =>
    let I := Ind A Cs' s in
    constr 0 s C /\
    forall Δ σ, [ Δ |- σ -| Γ ] ->
      [ Δ |- F.[σ] :- (dcase I Q (Constr i I) C).[σ] ])
    n Fs Cs ->
  [ Δ |- σ -| Γ ] ->
  All2i (fun i F C =>
    let I := Ind A.[σ] Cs'..[up σ] s in
    constr 0 s C /\
    [ Δ |- F :-dcase I Q.[σ] (Constr i I) C ])
  n Fs..[σ] Cs..[up σ].
Proof.
  elim: Fs Γ Δ n s A Q Cs σ.
  move=> Γ Δ n s A Q Cs σ h. inv h.
    constructor.
  move=> F Fs ih Γ Γ' n s A Q Cs σ h ag.
  destruct Cs; inv h. inv H3; asimpl.
  constructor. split.
  - apply: constr_subst; eauto.
    apply: n_subst0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold dcase in H0.
    erewrite constr_drespine_subst in H0; eauto.
    asimpl in H0.
    by unfold dcase; asimpl.
    asimpl; eauto.
    move=> i; discriminate.
  - apply: ih; eauto.
Qed.

Lemma substitution Γ Δ σ m A :
  [ Γ |- m :- A ] ->
  [ Δ |- σ -| Γ ] ->
  [ Δ |- m.[σ] :- A.[σ] ].
Proof with eauto using List.Forall.
  move=> ty. move: Γ m A ty Δ σ.
  apply: has_type_nested_ind=>//=.
  move=> Γ s l p Δ σ ag.
    apply: u_Sort.
    apply: agree_subst_pure...
  move=> Γ A B s l p tyA ihA tyB ihB Δ σ ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_u A ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: u_Prod...
    apply: agree_subst_pure...
  move=> Γ A B s l p tyA ihA tyB ihB Δ σ ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_n ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: l_Prod...
    apply: agree_subst_pure...
  move=> Γ A B s l p tyA ihA tyB ihB Δ σ ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_u A ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: u_Lolli...
    apply: agree_subst_pure...
  move=> Γ A B s l p tyA ihA tyB ihB Δ σ ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_n ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: l_Lolli...
    apply: agree_subst_pure...
  move=> Γ x A h Δ σ ag.
    apply: agree_subst_hasU...
  move=> Γ x A h Δ sigam ag.
    apply: agree_subst_hasL...
  move=> Γ n A B s t l p tyProd ihProd tyN ihN Δ σ ag.
    destruct s.
    move: (agree_subst_u A ag)=>ag'.
      move: (ihN _ _ ag')=>{ag'}tyN.
      apply: u_Lam...
      apply: agree_subst_pure...
    move: (agree_subst_l A ag)=>ag'.
      move: (ihN _ _ ag')=>{ag'}tyN.
      apply: u_Lam...
      apply: agree_subst_pure...
  move=> Γ n A B s t l tyLolli ihLolli tyN ihN Δ σ ag.
    move: (agree_subst_re_re ag)=>ag'.
    move: (ihLolli _ _ ag')=>{}ihLolli.
    destruct s.
    move: (agree_subst_u A ag)=>{}ag.
      move: (ihN _ _ ag)=>{}ihN.
      apply: l_Lam...
    move: (agree_subst_l A ag)=>{}ag.
      move: (ihN _ _ ag)=>{}ihN.
      apply: l_Lam...
  move=> Γ1 Γ2 Γ A B m n p tyM ihM tyN ihN mg Δ σ ag.
    replace B.[n/].[σ] 
      with (B.[up σ]).[n.[σ]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Δ1[Δ2[mg'[ag1 ag2]]]].
    move: (agree_subst_pure ag2 p)=>{}p.
    apply: u_Prod_App...
  move=> Γ1 Γ2 Γ A B m n tyM ihM tyN ihN mg Δ σ ag.
    replace B.[n/].[σ]
      with (B.[up σ]).[n.[σ]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Δ1[Δ2[mg'[ag1 ag2]]]].
    apply: l_Prod_App...
  move=> Γ1 Γ2 Γ A B m n p tyM ihM tyN ihN mg Δ σ ag.
    replace B.[n/].[σ] 
      with (B.[up σ]).[n.[σ]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Δ1[Δ2[mg'[ag1 ag2]]]].
    move: (agree_subst_pure ag2 p)=>{}p.
    apply: u_Lolli_App...
  move=> Γ1 Γ2 Γ A B m n tyM ihM tyN ihN mg Δ σ ag.
    replace B.[n/].[σ]
      with (B.[up σ]).[n.[σ]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Δ1[Δ2[mg'[ag1 ag2]]]].
    apply: l_Lolli_App...
  move=> Γ A s Cs l ar cs p tyA ihA tyCs ihCs Δ σ ag.
    apply: s_Ind...
    apply: arity_subst...
    elim: cs; asimpl...
      move=> C Cs' c hd tl.
      constructor...
      apply: constr_subst...
      apply: n_subst0.
    apply: agree_subst_pure...
    elim: ihCs; asimpl...
      move=> C Cs' hd tl ih.
      constructor...
      apply: hd.
      constructor...
  move=> Γ A s i C Cs ig p ty ih Δ σ ag; asimpl.
    replace C.[Ind A.[σ] Cs..[up σ] s .: σ]
      with C.[up σ].[Ind A.[σ] Cs..[up σ] s/]
      by autosubst.
    apply: s_Constr...
    apply: iget_subst...
    apply: agree_subst_pure...
  move=> Γ1 Γ2 Γ A Q s s' Fs Cs m ms a mg
    tyM ihM tyQ ihQ tyFsCs ihFsCs Δ σ ag.
    rewrite spine_subst.
    move: (merge_agree_subst_inv ag mg)=>[Δ1[Δ2[mg'[ag1 ag2]]]].
    move: (arity_subst σ a)=> a'.
    move: (agree_subst_re_re ag2)=> ag2'.
    move: (ihQ _ _ ag2')=> {}ihQ.
    erewrite arity1_subst in ihQ...
    move: (ihM _ _ ag1)=> {}ihM.
    rewrite spine_subst in ihM.
    apply: s_Case...
    apply: All2_case_subst...
  move=> Γ1 Γ2 Γ A Q s Fs Cs m ms a p mg
    tyM ihM tyQ ihQ tyFsCs ihFsCs Δ σ ag.
    rewrite spine_subst.
    move: (merge_agree_subst_inv ag mg)=>[Δ1[Δ2[mg'[ag1 ag2]]]].
    move: (arity_subst σ a)=> a'.
    move: (agree_subst_re_re ag2)=> ag2'.
    move: (ihQ _ _ ag2')=> {}ihQ.
    erewrite arity2_subst in ihQ...
    move: (ihM _ _ ag1)=> {}ihM.
    rewrite spine_subst in ihM.
    move: (agree_subst_pure ag1 p)=>{}p.
    apply: s_DCase...
    apply: All2i_dcase_subst...
  move=> Γ A m l p tyA ihA tyM ihM Δ σ ag.
    apply: u_Fix...
    apply: agree_subst_pure...
    have ag' : [ A.[σ] +u Δ |- up σ -| A +u Γ ].
      by constructor.
    move: (ihM _ _ ag'); asimpl=>//.
  move=> Γ A B m s l sub tyB ihB tyM ihM Δ σ ag.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub.
    apply: ihB.
    by apply: agree_subst_re_re.
    by apply: ihM.
Qed.

Lemma substitutionU Γ1 Γ2 Γ m n A B :
  [ A +u Γ1 |- m :- B ] ->
  [ Γ2 |- n :- A ] ->
  pure Γ2 ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN p mg.
  apply: substitution; eauto.
  move: (merge_pure2 mg p)=>->.
  apply: agree_subst_wkU.
  apply: agree_subst_refl.
  move: (merge_re_re mg)=>[-><-].
  asimpl.
  by rewrite <- pure_re.
Qed.

Lemma substitutionN Γ1 Γ2 m n A B :
  [ +n Γ1 |- m :- B ] ->
  [ Γ2 |- n :- A ] ->
  [ Γ1 |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN.
  apply: substitution; eauto.
  apply: agree_subst_wkN.
  apply: agree_subst_refl.
Qed.

Lemma substitutionL Γ1 Γ2 Γ m n A B :
  [ A +l Γ1 |- m :- B ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN mg.
  apply: substitution; eauto.
  apply: agree_subst_wkL; asimpl; eauto.
  apply: agree_subst_refl.
Qed.

Lemma context_convU Γ m A B C l :
  B === A ->
  [ re Γ |- A :- Sort U l ] ->
  [ A +u Γ |- m :- C ] ->
  [ B +u Γ |- m :- C ].
Proof.
  move=> e tyA tyM.
  cut [ B +u Γ |- m.[ids] :- C.[ids] ]. 
    by autosubst.
  apply: substitution; eauto.
  apply: agree_subst_convU; asimpl.
  apply: conv_sub; eauto.
  move: (weakeningU B tyA); asimpl; eauto.
  apply: agree_subst_refl.
Qed.

Lemma context_convL Γ m A B C l :
  B === A ->
  [ re Γ |- A :- Sort L l ] ->
  [ A +l Γ |- m :- C ] ->
  [ B +l Γ |- m :- C ].
Proof.
  move=> e tyA tyB.
  cut [ B +l Γ |- m.[ids] :- C.[ids] ].
    by autosubst.
  apply: substitution; eauto.
  apply: agree_subst_convL; asimpl.
  apply: conv_sub; eauto.
  move: (weakeningN tyA); asimpl; eauto.
  eauto.
  apply: agree_subst_refl.
Qed.