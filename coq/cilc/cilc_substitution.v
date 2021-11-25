From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ Delta |- sigma -| Gamma ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil sigma :
  [ nil |- sigma -| nil ]
| agree_subst_u Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] +u Delta |- up sigma -| A +u Gamma ]
| agree_subst_l Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] +l Delta |- up sigma -| A +l Gamma ]
| agree_subst_n Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ +n Delta |- up sigma -| +n Gamma ]
| agree_subst_wkU Delta sigma Gamma n A :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- n :- A.[sigma] ] ->
  [ Delta |- n .: sigma -| A +u Gamma ]
| agree_subst_wkL Delta1 Delta2 Delta sigma Gamma n A :
  merge Delta1 Delta2 Delta ->
  [ Delta1 |- sigma -| Gamma ] ->
  [ Delta2 |- n :- A.[sigma] ] ->
  [ Delta |- n .: sigma -| A +l Gamma ]
| agree_subst_wkN Delta sigma Gamma n :
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- n .: sigma -| +n Gamma ]
| agree_subst_convU Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[sigma] :- Sort U l ] ->
  [ Delta |- sigma -| A +u Gamma ] ->
  [ Delta |- sigma -| B +u Gamma ]
| agree_subst_convL Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[sigma] :- Sort L l ] ->
  [ re Gamma |- B :- Sort L l ] ->
  [ Delta |- sigma -| A +l Gamma ] ->
  [ Delta |- sigma -| B +l Gamma ]
where "[ Delta |- sigma -| Gamma ]" := (agree_subst Delta sigma Gamma).

Lemma agree_subst_pure Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] -> pure Gamma -> pure Delta.
Proof with eauto using pure.
  elim=>//=...
  move=> Delta' sigma' Gamma' A ag h p. inv p...
  move=> Delta' sigma' Gamma' A ag h p. inv p.
  move=> Delta' sigma' Gamma' ag h p. inv p...
  move=> Delta' sigma' Gamma' n A ag1 h ag2 p. inv p...
  move=> Delta1 Delta2 Delta' sigma' Gamma' n A mg ag1 h ag2 p. inv p.
  move=> Delta' sigma' Gamma' _ ag h p. inv p...
  move=> Delta' sigma' Gamma' A B l sb ag1 ag2 h p. inv p...
  move=> Delta' sigma' Gamma' A B l sb ty1 ty2 ag h p. inv p.
Qed.

Lemma agree_subst_refl Gamma : [ Gamma |- ids -| Gamma ].
Proof with eauto using agree_subst.
  elim: Gamma...
  move=> a Gamma ag.
  destruct a.
  destruct p.
  destruct s.
  replace [ t +u Gamma |- ids -| t +u Gamma ]
    with [ t.[ids] +u Gamma |- up ids -| t +u Gamma ]
    by autosubst...
  replace [ t +l Gamma |- ids -| t +l Gamma ]
    with [ t.[ids] +l Gamma |- up ids -| t +l Gamma ]
    by autosubst...
  replace ids with (up ids) by autosubst...
Qed.

Lemma agree_subst_hasU Delta sigma Gamma x A :
  [ Delta |- sigma -| Gamma ] ->
  hasU Gamma x A ->
  [ Delta |- sigma x :- A.[sigma] ].
Proof.
  move=> ag. elim: ag x A=>{sigma Delta Gamma}.
  move=> sigma x A h. inv h.
  move=> Delta sigma Gamma A ag ih x A' h. inv h; asimpl.
    apply: u_Var.
    replace (A.[sigma >> ren (+1)])
      with (A.[sigma].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_subst_pure; eauto.
    apply: eweakeningU; eauto. autosubst.
  move=> Delta sigma Gamma A ag ih x A' h. inv h.
  move=> Delta sigma Gamma Ag ih x A h. inv h.
    apply: eweakeningN; eauto; autosubst.
  move=> Delta sigma Gamma n A ag ih ty x A' h. 
    inv h; asimpl; eauto.
    have p := agree_subst_pure ag H3.
    by rewrite (pure_re p).
  move=> Delta1 Delta2 Delta sigma Gamma n A mg ag ih ty x A' h. 
    inv h.
  move=> Delta sigma Gamma n ag ih x A h. inv h; asimpl; eauto.
  move=> Delta sigma Gamma A B l sb ty ag ih x A' h. inv h.
    have h' : hasU (A +u Gamma) 0 A.[ren (+1)].
      constructor; eauto.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub_ren; eauto.
    apply: ty.
    apply: ih; eauto.
    apply: ih.
    constructor; eauto.
  move=> Delta sigma Gamma A B l sb t1 ty2 ag ih x A' h.
    inv h.
Qed.

Lemma agree_subst_hasL Delta sigma Gamma x A :
  [ Delta |- sigma -| Gamma ] ->
  hasL Gamma x A ->
  [ Delta |- sigma x :- A.[sigma] ].
Proof.
  move=> ag. elim: ag x A=>{Delta sigma Gamma}.
  move=> sigma x A h. inv h.
  move=> Delta sigma Gamma A ag ih x A' h. inv h.
    apply: eweakeningU; eauto; autosubst.
  move=> Delta sigma Gamma A ag ih x A' h. inv h; asimpl.  
    replace (A.[sigma >> ren (+1)])
      with (A.[sigma].[ren (+1)]) by autosubst.
    apply: l_Var.
    constructor.
    apply: agree_subst_pure; eauto.
  move=> Delta sigma Gamma ag ih x A h. inv h.
    apply: eweakeningN; eauto; autosubst.
  move=> Delta sigma Gamma n A ag ih ty x A' h. 
    inv h; asimpl; eauto.
  move=> Delta1 Delta2 Delta sigma Gamma n A mg ag ih ty x A' h.
    inv h; asimpl.
    have p := agree_subst_pure ag H3.
    rewrite (merge_pure1 mg p); eauto.
  move=> Delta sigma Gamma n ag ih x A h. inv h; asimpl; eauto.
  move=> Delta sigma Gamma A B l sb ty ag ih x A' h. inv h.
    apply: ih.
    constructor; eauto.
  move=> Delta sigma Gamma A B l sb ty1 ty2 ag ih x A' h. inv h.
    have h' : hasL (A +l Gamma) 0 A.[ren (+1)].
      constructor; eauto.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub_ren; eauto.
    apply: ty1.
    apply: ih; eauto.
Qed.

Lemma agree_subst_re_re Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- sigma -| re Gamma ].
Proof with eauto using agree_subst.
  move=> ag. elim: ag=>//={Delta sigma Gamma}...
  move=> Delta sigma Gamma n A ag1 ag2 ty.
    constructor...
    rewrite <- re_re...
  move=> Delta1 Delta2 Delta sigma Gamma n A mg ag1 ag2 ty.
    constructor...
    move: (merge_re_re mg)=>[<-_]...
  move=> Delta sigma Gamma A B l sb ty ag1 ag2.
    apply: agree_subst_convU...
    rewrite <- re_re...
Qed.

Lemma merge_agree_subst_inv Delta sigma Gamma1 Gamma2 Gamma :
  [ Delta |- sigma -| Gamma ] ->
  merge Gamma1 Gamma2 Gamma ->
  exists Delta1 Delta2,
    merge Delta1 Delta2 Delta /\
    [ Delta1 |- sigma -| Gamma1 ] /\
    [ Delta2 |- sigma -| Gamma2 ].
Proof.
  move=> ag. elim: ag Gamma1 Gamma2=>{Delta sigma Gamma}.
  move=> sigma Gamma1 Gamma2 mg. inv mg.
    exists nil. exists nil. repeat constructor; eauto.
  move=> Delta sigma Gamma A ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists (A.[sigma] +u Delta1).
    exists (A.[sigma] +u Delta2).
    repeat constructor; eauto.
  move=> Delta sigma Gamma A ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists (A.[sigma] +l Delta1).
      exists (+n Delta2).
      repeat constructor; eauto.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists (+n Delta1).
      exists (A.[sigma] +l Delta2).
      repeat constructor; eauto.
  move=> Delta sigma Gamma ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists (+n Delta1).
    exists (+n Delta2).
    repeat constructor; eauto.
  move=> Delta sigma Gamma n A ag ih ty Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists Delta1. 
    exists Delta2.
    move: (merge_re_re mg')=>[e1 e2]. 
    repeat constructor; eauto.
    move: e1=>->; eauto.
    move: e2=>->; eauto.
  move=> Delta1 Delta2 Delta sigma Gamma n A mg1 ag ih ty
    Gamma1 Gamma2 mg2. inv mg2.
    move: (ih _ _ H2)=> {H2}[Delta1'[Delta2'[mg'[ag1 ag2]]]].
      move: (merge_split1 mg1 mg')=>[Delta'[mg1' mg2']].
      exists Delta'. 
      exists Delta2'.
      repeat constructor; eauto.
      apply: agree_subst_wkL; eauto.
    move: (ih _ _ H2)=> {H2}[Delta1'[Delta2'[mg'[ag1 ag2]]]].
      move: (merge_split2 mg1 mg')=>[Delta'[mg1' mg2']].
      exists Delta1'.
      exists Delta'.
      repeat constructor; eauto.
      apply: agree_subst_wkL; eauto.
  move=> Delta sigma Gamma n ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists Delta1.
    exists Delta2.
    repeat constructor; eauto.
  move=> Delta sigma Gamma A B l sb ty ag ih Gamma1 Gamma2 mg.
    inv mg.
    have mg : merge (A +u Gamma0) (A +u Gamma3) (A +u Gamma).
      constructor; eauto.
    move: (ih _ _ mg)=>{mg}[Delta1[Delta2[mg[ag1 ag2]]]].
    exists Delta1.
    exists Delta2.
    move: (merge_re_re mg)=>[e1 e2].
    repeat constructor; eauto.
    apply: agree_subst_convU; eauto.
    rewrite e1; eauto.
    apply: agree_subst_convU; eauto.
    rewrite e2; eauto.
  move=> Delta sigma Gamma A B l sb ty1 ty2 ag ih Gamma1 Gamma2 mg.
    inv mg.
    have mg' : merge (A +l Gamma0) (+n Gamma3) (A +l Gamma).
      constructor; eauto.
      move: (ih _ _ mg')=>{mg'}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists Delta1.
      exists Delta2.
      move: (merge_re_re H2)=>[eG1 eG2].
      move: (merge_re_re mg')=>[eD1 eD2].
      repeat constructor; eauto.
      apply: agree_subst_convL; eauto.
      move: eD1=>->; eauto.
      move: eG1=>->; eauto.
    have mg' : merge (+n Gamma0) (A +l Gamma3) (A +l Gamma).
      constructor; eauto.
      move: (ih _ _ mg')=>{mg'}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists Delta1.
      exists Delta2.
      move: (merge_re_re H2)=>[eG1 eG2].
      move: (merge_re_re mg')=>[eD1 eD2].
      repeat constructor; eauto.
      apply: agree_subst_convL; eauto.
      move: eD2=>->; eauto.
      move: eG2=>->; eauto.
Qed.

Lemma arity_subst s A sigma :
  arity s A -> arity s A.[sigma].
Proof with eauto using arity.
  move=> ar. elim: ar sigma...
Qed.

Definition n_subst sigma x := 
  (forall i, ~x = i -> noccurs x (sigma i)) /\ sigma x = Var x.

Lemma noccurs_ren0 x m xi :
  (forall i, ~xi i = x) -> noccurs x m.[ren xi].
Proof with eauto using noccurs, List.Forall.
  move: m x xi. apply: term_ind_nested...
  move=> A B s ihA ihB x xi h; asimpl.
    constructor...
    apply: ihB=> i.
    destruct i; asimpl; eauto.
  move=> A B s ihA ihB x xi h; asimpl.
    constructor...
    apply: ihB=> i.
    destruct i; asimpl; eauto.
  move=> A m s ihA ihM x xi h; asimpl.
    constructor...
    apply: ihM=> i.
    destruct i; asimpl; eauto.
  move=> A Cs s ihA ihCs x xi h; asimpl.
    constructor...
    elim: ihCs...
    move=> C Cs' hd tl ih.
    constructor...
    apply: hd=> i.
    destruct i; asimpl; eauto.
  move=> m Q Fs ihM ihQ ihFs x xi h; asimpl.
    constructor...
    elim: ihFs...
  move=> m Q Fs ihM ihQ ihFs x xi h; asimpl.
    constructor...
    elim: ihFs...
  move=> A m ihA ihM x xi h; asimpl.
    constructor...
    apply: ihM=> i.
    destruct i; asimpl; eauto.
Qed.

Lemma n_subst0 sigma : n_subst (up sigma) 0.
Proof.
  split; eauto.
  move=> i. elim: i sigma=>//=.
  move=> i _ sigma _; asimpl.
  apply: noccurs_ren0; eauto.
Qed.

Lemma noccurs_up x m xi :
  noccurs x m -> 
    (forall i, ~x = i -> ~xi x = xi i) -> 
    noccurs (xi x) m.[ren xi].
Proof with eauto using noccurs.
  move=> no. move: x m no xi.
  apply: noccurs_ind_nested=>//=... 
  move=> x A B s noA ihA noB ihB xi h.
    constructor; asimpl; eauto.
    apply: ihB=> i. 
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A B s noA ihA noB ihB xi h.
    constructor; asimpl; eauto.
    apply: ihB=> i. 
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A m s noA ihA noM ihM xi h.
    constructor; asimpl; eauto.
    apply: ihM=> i.
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A Cs s noA ihA noCs ihCs xi h.
    constructor; asimpl; eauto.
    elim: ihCs.
    asimpl; constructor.
    move=> C Cs' hd tl ih; asimpl.
    constructor; eauto.
    apply: hd=> i neq.
    destruct i; asimpl; eauto.
    have /h neq' : ~x = i by eauto.
    eauto.
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs xi h.
    constructor; asimpl; eauto.
    elim: ihFs.
    asimpl; constructor.
    move=> F Fs' hd tl ih; asimpl.
    constructor; eauto.
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs xi h.
    constructor; asimpl; eauto.
    elim: ihFs.
    asimpl; constructor.
    move=> F Fs' hd tl ih; asimpl.
    constructor; eauto.
  move=> x A m noA ihA noM ihM xi h.
    constructor; asimpl; eauto.
    apply: ihM=> i neq.
    destruct i; asimpl; eauto.
    have /h neq' : ~x = i by eauto.
    eauto.
Qed.

Lemma n_subst_up sigma x :
  n_subst sigma x -> n_subst (up sigma) x.+1.
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

Lemma noccurs_subst sigma m x :
  noccurs x m -> n_subst sigma x -> noccurs x m.[sigma].
Proof with eauto using noccurs.
  move=> no. move: x m no sigma.
  apply: noccurs_ind_nested=>//=...
  move=> x y neq sigma [n _]...
  move=> x A B s noA ihA noB ihB sigma no.
    constructor...
    apply: ihB...
    apply: n_subst_up...
  move=> x A B s noA ihA noB ihB sigma no.
    constructor...
    apply: ihB...
    apply: n_subst_up...
  move=> x A m s noA ihA noM ihM sigma no.
    constructor...
    apply: ihM...
    apply: n_subst_up...
  move=> x A Cs s noA ihA noCs ihCs sigma no.
    constructor...
    elim: ihCs noCs; asimpl.
    constructor.
    move=> C Cs' hd tl ih1 ih2. inv ih2.
    constructor...
    apply: hd.
    apply: n_subst_up...
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs sigma no.
    constructor...
    elim: ihFs noFs; asimpl.
    constructor.
    move=> F Fs' hd tl ih1 ih2. inv ih2.
    constructor...
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs sigma no.
    constructor...
    elim: ihFs noFs; asimpl.
    constructor.
    move=> F Fs' hd tl ih1 ih2. inv ih2.
    constructor...
  move=> x A m noA ihA noM ihM sigma no.
    constructor...
    apply: ihM.
    apply: n_subst_up...
Qed.

Lemma pos_subst i A sigma :
  pos i A -> n_subst sigma i -> pos i A.[sigma].
Proof with eauto.
  move=> p. elim: p sigma=>//={i A}.
  move=> x ms noMs sigma [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: noMs.
    constructor.
    move=> m ms' noM noMs ihMs; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B s noA pB ihB sigma n.
    constructor.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B s noA pB ihB sigma n.
    constructor.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
Qed.

Lemma active_subst i m sigma :
  active i m -> n_subst sigma i -> active i m.[sigma].
Proof with eauto using List.Forall.
  move=> a. elim: a sigma=>{i m}=>//=.
  move=> x ms no sigma [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no...
    move=> m ms' hd tl ih; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B s p a ihB nB sigma n.
    apply: active_Pos.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B s noA a ihB sigma n.
    apply: active_Lolli.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
Qed.

Lemma constr_subst i s (m : term) sigma :
  constr i s m -> n_subst sigma i -> constr i s m.[sigma].
Proof with eauto.
  move=> c. elim: c sigma=>{i s m}=>//=.
  move=> x s ms no sigma [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no.
    constructor.
    move=> m ms' hd tl ih; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B p cB ihB nB sigma n.
    apply: constr_UPos.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B noA cB ihB sigma n.
    apply: constr_UProd.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B p cB ihB nB sigma n.
    apply: constr_LPos1.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B p a noB sigma n.
    apply: constr_LPos2.
    apply: pos_subst...
    apply: active_subst...
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B noA cB ihB sigma n.
    apply: constr_LProd1.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B noA a sigma n.
    apply: constr_LProd2.
    apply: noccurs_subst...
    apply: active_subst...
    apply: n_subst_up...
Qed.

Lemma arity1_subst s s' A sigma :
  arity s A -> (arity1 s' A).[sigma] = arity1 s' A.[sigma].
Proof.
  move=> a. elim: a sigma s'=>//={A}.
  move=> A B a ih sigma s'.
  rewrite ih; eauto.
Qed.

Lemma arity2_subst s s' I A sigma :
  arity s A -> (arity2 s' I A).[sigma] = arity2 s' I.[sigma] A.[sigma].
Proof.
  move=> a. elim: a I sigma s'=>//={A}.
  move=> A B a ih I sigma s'; asimpl.
  rewrite ih; asimpl; eauto.
Qed.

Lemma respine_I_subst Q I sigma :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  Q.[sigma] = respine Q.[sigma] I.[sigma].
Proof.
  elim: I sigma Q=>//=.
  move=> x sigma Q _ h.
    move: (h x)=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi Q h _.
    move: (h (Var 0))=>//=.
Qed.

Lemma drespine_I_subst Q c I sigma :
  (forall Q, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  App Q.[sigma] c.[sigma] = drespine Q.[sigma] c.[sigma] I.[sigma].
Proof.
  elim: I sigma Q=>//=.
  move=> x sigma Q _ h.
    move: (h x)=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi Q h _.
    move: (h (Var 0))=>//=.
Qed.

Lemma respine_spine'_I_subst Q I ms sigma :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine Q (spine' I ms)).[sigma] =
    respine Q.[sigma] (spine' I ms).[sigma].
Proof.
  elim: ms Q I sigma=>//=.
  move=> Q I sigma h1 h2.
    rewrite h1.
    by apply: respine_I_subst.
  move=> m ms ih Q I xi h1 h2.
    rewrite ih; eauto.
Qed.

Lemma drespine_spine'_I_subst Q c I ms sigma :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  (drespine Q c (spine' I ms)).[sigma] =
    drespine Q.[sigma] c.[sigma] (spine' I ms).[sigma].
Proof.
  elim: ms Q I sigma=>//=.
  move=> Q I sigma h1 h2.
    rewrite h1.
    by apply: drespine_I_subst.
  move=> m ms ih Q I xi h1 h2.
    repeat f_equal.
    apply: respine_spine'_I_subst; eauto.
    by apply: drespine_respine.
Qed.

Lemma respine_spine_I_subst Q I ms sigma :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine Q (spine I ms)).[sigma] =
    respine Q.[sigma] (spine I ms).[sigma].
Proof.
  move=> h1 h2.
  rewrite spine_spine'_rev.
  by rewrite respine_spine'_I_subst.
Qed.

Lemma drespine_spine_I_subst Q c I ms sigma :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  (drespine Q c (spine I ms)).[sigma] =
    drespine Q.[sigma] c.[sigma] (spine I ms).[sigma].
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

Lemma active_respine_subst n (A Q C : term) Cs I sigma :
  active n C ->
  I n = Ind A Cs L ->
  (forall x, ~I n = Var x) ->
  (respine Q C.[I]).[sigma] =
    respine Q.[sigma] C.[I].[sigma].
Proof.
  move=> c.
  elim: c A Q Cs I sigma; intros.
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

Lemma active_drespine_subst n (A Q c C : term) Cs I sigma :
  active n C ->
  I n = Ind A Cs L ->
  (forall x, ~I n = Var x) ->
  (drespine Q c C.[I]).[sigma] =
    drespine Q.[sigma] c.[sigma] C.[I].[sigma].
Proof.
  move=> a.
  elim: a c Q I sigma; intros.
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

Lemma constr_respine_subst n (A Q C : term) Cs I sigma s :
  constr n s C ->
  I n = Ind A Cs s ->
  (forall x, ~I n = Var x) ->
  (respine Q C.[I]).[sigma] =
    respine Q.[sigma] C.[I].[sigma].
Proof.
  move=> c.
  elim: c A Q Cs I sigma; intros.
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

Lemma constr_drespine_subst n s (A Q c C : term) Cs I sigma :
  constr n s C ->
  I n = Ind A Cs s ->
  (forall x, ~I n = Var x) ->
  (drespine Q c C.[I]).[sigma] =
    drespine Q.[sigma] c.[sigma] C.[I].[sigma].
Proof.
  move=> cn.
  elim: cn A Q c Cs I sigma; intros.
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

Lemma All2_case_subst Gamma Delta s A Q Fs Cs Cs' sigma :
  All2 (fun F C =>
    constr 0 s C /\
    forall Delta sigma, [ Delta |- sigma -| Gamma ] ->
      [ Delta |- F.[sigma] :- (case (Ind A Cs' s) Q C).[sigma] ])
    Fs Cs ->
  [ Delta |- sigma -| Gamma ] ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Delta |- F :- case (Ind A.[sigma] Cs'..[up sigma] s) Q.[sigma] C])
  Fs..[sigma] Cs..[up sigma].
Proof.
  elim: Fs Gamma Delta s A Q Cs sigma.
  move=> Gamma Delta s A Q Cs sigma h. inv h.
    constructor.
  move=> F Fs ih Gamma Delta s A Q Cs sigma h ag.
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

Lemma All2i_dcase_subst Gamma Delta n s A Q Fs Cs Cs' sigma :
  All2i (fun i F C =>
    let I := Ind A Cs' s in
    constr 0 s C /\
    forall Delta sigma, [ Delta |- sigma -| Gamma ] ->
      [ Delta |- F.[sigma] :- (dcase I Q (Constr i I) C).[sigma] ])
    n Fs Cs ->
  [ Delta |- sigma -| Gamma ] ->
  All2i (fun i F C =>
    let I := Ind A.[sigma] Cs'..[up sigma] s in
    constr 0 s C /\
    [ Delta |- F :-dcase I Q.[sigma] (Constr i I) C ])
  n Fs..[sigma] Cs..[up sigma].
Proof.
  elim: Fs Gamma Delta n s A Q Cs sigma.
  move=> Gamma Delta n s A Q Cs sigma h. inv h.
    constructor.
  move=> F Fs ih Gamma Gamma' n s A Q Cs sigma h ag.
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

Lemma substitution Gamma Delta sigma m A :
  [ Gamma |- m :- A ] ->
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- m.[sigma] :- A.[sigma] ].
Proof with eauto using List.Forall.
  move=> ty. move: Gamma m A ty Delta sigma.
  apply: has_type_nested_ind=>//=.
  move=> Gamma s l p Delta sigma ag.
    apply: u_Sort.
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_u A ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: u_Prod...
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_n ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: l_Prod...
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_u A ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: u_Lolli...
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_n ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: l_Lolli...
    apply: agree_subst_pure...
  move=> Gamma x A h Delta sigma ag.
    apply: agree_subst_hasU...
  move=> Gamma x A h Delta sigam ag.
    apply: agree_subst_hasL...
  move=> Gamma n A B s t l p tyProd ihProd tyN ihN Delta sigma ag.
    destruct s.
    move: (agree_subst_u A ag)=>ag'.
      move: (ihN _ _ ag')=>{ag'}tyN.
      apply: u_Lam...
      apply: agree_subst_pure...
    move: (agree_subst_l A ag)=>ag'.
      move: (ihN _ _ ag')=>{ag'}tyN.
      apply: u_Lam...
      apply: agree_subst_pure...
  move=> Gamma n A B s t l tyLolli ihLolli tyN ihN Delta sigma ag.
    move: (agree_subst_re_re ag)=>ag'.
    move: (ihLolli _ _ ag')=>{}ihLolli.
    destruct s.
    move: (agree_subst_u A ag)=>{}ag.
      move: (ihN _ _ ag)=>{}ihN.
      apply: l_Lam...
    move: (agree_subst_l A ag)=>{}ag.
      move: (ihN _ _ ag)=>{}ihN.
      apply: l_Lam...
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma] 
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (agree_subst_pure ag2 p)=>{}p.
    apply: u_Prod_App...
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma]
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    apply: l_Prod_App...
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma] 
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (agree_subst_pure ag2 p)=>{}p.
    apply: u_Lolli_App...
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma]
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    apply: l_Lolli_App...
  move=> Gamma A s Cs l ar cs p tyA ihA tyCs ihCs Delta sigma ag.
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
  move=> Gamma A s i C Cs ig p ty ih Delta sigma ag; asimpl.
    replace C.[Ind A.[sigma] Cs..[up sigma] s .: sigma]
      with C.[up sigma].[Ind A.[sigma] Cs..[up sigma] s/]
      by autosubst.
    apply: s_Constr...
    apply: iget_subst...
    apply: agree_subst_pure...
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms a mg
    tyM ihM tyQ ihQ tyFsCs ihFsCs Delta sigma ag.
    rewrite spine_subst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (arity_subst sigma a)=> a'.
    move: (agree_subst_re_re ag2)=> ag2'.
    move: (ihQ _ _ ag2')=> {}ihQ.
    erewrite arity1_subst in ihQ...
    move: (ihM _ _ ag1)=> {}ihM.
    rewrite spine_subst in ihM.
    apply: s_Case...
    apply: All2_case_subst...
  move=> Gamma1 Gamma2 Gamma A Q s Fs Cs m ms a p mg
    tyM ihM tyQ ihQ tyFsCs ihFsCs Delta sigma ag.
    rewrite spine_subst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (arity_subst sigma a)=> a'.
    move: (agree_subst_re_re ag2)=> ag2'.
    move: (ihQ _ _ ag2')=> {}ihQ.
    erewrite arity2_subst in ihQ...
    move: (ihM _ _ ag1)=> {}ihM.
    rewrite spine_subst in ihM.
    move: (agree_subst_pure ag1 p)=>{}p.
    apply: s_DCase...
    apply: All2i_dcase_subst...
  move=> Gamma A m l p tyA ihA tyM ihM Delta sigma ag.
    apply: u_Fix...
    apply: agree_subst_pure...
    have ag' : [ A.[sigma] +u Delta |- up sigma -| A +u Gamma ].
      by constructor.
    move: (ihM _ _ ag'); asimpl=>//.
  move=> Gamma A B m s l sub tyB ihB tyM ihM Delta sigma ag.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub.
    apply: ihB.
    by apply: agree_subst_re_re.
    by apply: ihM.
Qed.

Lemma substitutionU Gamma1 Gamma2 Gamma m n A B :
  [ A +u Gamma1 |- m :- B ] ->
  [ Gamma2 |- n :- A ] ->
  pure Gamma2 ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- m.[n/] :- B.[n/] ].
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

Lemma substitutionN Gamma1 Gamma2 m n A B :
  [ +n Gamma1 |- m :- B ] ->
  [ Gamma2 |- n :- A ] ->
  [ Gamma1 |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN.
  apply: substitution; eauto.
  apply: agree_subst_wkN.
  apply: agree_subst_refl.
Qed.

Lemma substitutionL Gamma1 Gamma2 Gamma m n A B :
  [ A +l Gamma1 |- m :- B ] ->
  [ Gamma2 |- n :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN mg.
  apply: substitution; eauto.
  apply: agree_subst_wkL; asimpl; eauto.
  apply: agree_subst_refl.
Qed.

Lemma context_convU Gamma m A B C l :
  B === A ->
  [ re Gamma |- A :- Sort U l ] ->
  [ A +u Gamma |- m :- C ] ->
  [ B +u Gamma |- m :- C ].
Proof.
  move=> e tyA tyM.
  cut [ B +u Gamma |- m.[ids] :- C.[ids] ]. 
    by autosubst.
  apply: substitution; eauto.
  apply: agree_subst_convU; asimpl.
  apply: conv_sub; eauto.
  move: (weakeningU B tyA); asimpl; eauto.
  apply: agree_subst_refl.
Qed.

Lemma context_convL Gamma m A B C l :
  B === A ->
  [ re Gamma |- A :- Sort L l ] ->
  [ A +l Gamma |- m :- C ] ->
  [ B +l Gamma |- m :- C ].
Proof.
  move=> e tyA tyB.
  cut [ B +l Gamma |- m.[ids] :- C.[ids] ].
    by autosubst.
  apply: substitution; eauto.
  apply: agree_subst_convL; asimpl.
  apply: conv_sub; eauto.
  move: (weakeningN tyA); asimpl; eauto.
  eauto.
  apply: agree_subst_refl.
Qed.