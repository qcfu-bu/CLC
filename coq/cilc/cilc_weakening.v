From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil xi :
  agree_ren xi nil nil
| agree_ren_u Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m +u Gamma) (m.[ren xi] +u Gamma')
| agree_ren_l Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m +l Gamma) (m.[ren xi] +l Gamma')
| agree_ren_n Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (+n Gamma) (+n Gamma')
| agree_ren_wkU Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) Gamma (m +u Gamma')
| agree_ren_wkN Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) Gamma (+n Gamma').

Lemma agree_ren_refl Gamma : agree_ren id Gamma Gamma.
Proof.
  elim: Gamma.
  apply: agree_ren_nil.
  move=> a Gamma ag.
  destruct a.
  destruct p.
  destruct s.
  have h : (agree_ren id (t +u Gamma) (t +u Gamma)
    = agree_ren (upren id) (t +u Gamma) (t.[ren id] +u Gamma))
    by autosubst.
  rewrite h; constructor; eauto.
  have h : (agree_ren id (t +l Gamma) (t +l Gamma)
    = agree_ren (upren id) (t +l Gamma) (t.[ren id] +l Gamma))
    by autosubst.
  rewrite h; constructor; eauto.
  have h : (agree_ren id (+n Gamma) (+n Gamma)
    = agree_ren (upren id) (+n Gamma) (+n Gamma))
    by autosubst.
  rewrite h; constructor; eauto.
Qed.

Lemma agree_ren_pure Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' -> pure Gamma -> pure Gamma'.
Proof with eauto using pure.
  elim=>{Gamma Gamma' xi} //=...
  move=> Gamma Gamma' xi m ag ih pu.
    inv pu...
  move=> Gamma Gamma' xi m ag ih pu.
    inv pu.
  move=> Gamma Gamma' xi ag ih pu.
    inv pu...
Qed.

Lemma agree_ren_re_re Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' -> agree_ren xi (re Gamma) (re Gamma').
Proof. elim; eauto using agree_ren. Qed.

Lemma agree_ren_hasU Gamma Gamma' xi x A :
  agree_ren xi Gamma Gamma' ->
  hasU Gamma x A ->
  hasU Gamma' (xi x) A.[ren xi].
Proof with eauto.
  move=> ag. elim: ag x A=> {Gamma Gamma' xi}.
  move=> xi x A hs. inv hs.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_ren_pure...
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
  move=> Gamma Gamma' xi ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
Qed.

Lemma agree_ren_hasL Gamma Gamma' xi x A :
  agree_ren xi Gamma Gamma' ->
  hasL Gamma x A ->
  hasL Gamma' (xi x) A.[ren xi].
Proof with eauto.
  move=> ag. elim: ag x A=>{Gamma Gamma' xi}.
  move=> xi x A hs. inv hs.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_ren_pure...
  move=> Gamma Gamma' xi ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
Qed.

Lemma merge_agree_ren_inv Gamma1 Gamma2 Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
    merge Gamma1 Gamma2 Gamma ->
    exists Gamma1' Gamma2',
      merge Gamma1' Gamma2' Gamma' /\
      agree_ren xi Gamma1 Gamma1' /\
      agree_ren xi Gamma2 Gamma2'.
Proof with eauto.
  move=> ag. elim: ag Gamma1 Gamma2=>{Gamma Gamma' xi}.
  move=> xi Gamma1 Gamma2 mg. inv mg.
    exists nil. exists nil. repeat constructor.
  move=> Gamma Gamma' xi m ag ih Gamma1 Gamma2 mg. inv mg.
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (m.[ren xi] +u Gamma1').
    exists (m.[ren xi] +u Gamma2').
    repeat constructor...
  move=> Gamma Gamma' xi m ag ih Gamma1 Gamma2 mg. inv mg.
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (m.[ren xi] +l Gamma1').
    exists (+n Gamma2').
      repeat constructor...
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (+n Gamma1').
    exists (m.[ren xi] +l Gamma2').
      repeat constructor...
  move=> Gamma Gamma' xi ag ih Gamma1 Gamma2 mg. inv mg.
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (+n Gamma1').
    exists (+n Gamma2').
    repeat constructor...
  move=> Gamma Gamma' xi m ag ih Gamma1 Gamma2 mg.
    move: mg=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (m +u Gamma1').
    exists (m +u Gamma2').
    repeat constructor...
  move=> Gamma Gamma' xi ag ih Gamma1 Gamma2 mg.
    move: mg=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (+n Gamma1').
    exists (+n Gamma2').
    repeat constructor...
Qed.

Lemma arity_ren s A xi : arity s A -> arity s A.[ren xi].
Proof with eauto using arity.
  move=> ar. elim: ar xi=>//=...
  move=> A' B ar ih xi.
    constructor.
    replace (up (ren xi)) with (ren (upren xi)) by autosubst.
    exact: ih.
Qed.

Definition n_ren (xi : var -> var) x :=
  xi x = x /\ 
    forall i, (~x = i -> ~xi i = x) /\ (~i = 0 -> ~xi i = 0).

Lemma n_ren0 xi : n_ren (upren xi) 0.
Proof.
  split; eauto.
  move=> i. elim: i xi=>//=.
Qed.

Lemma n_ren_up xi x :
  n_ren xi x -> n_ren (upren xi) x.+1.
Proof.
  move=>[e h]. split.
  asimpl; eauto.
  elim; asimpl; eauto.
  move=> n [ih1 ih2]. split; eauto.
  move=> neq. 
  have pf : ~x = n by eauto.
  move: (h n)=>[h1 h2].
  move: pf=>/h1; eauto.
Qed.

Lemma noccurs_ren x m xi :
  noccurs x m -> n_ren xi x -> noccurs x m.[ren xi].
Proof with eauto using noccurs, n_ren_up, and.
  move=> no. move: x m no xi.
  apply: noccurs_ind_nested=>//=...
  move=> x y neq xi [e h].
    move: (h y)=> {h} [h _].
    move: neq=> /h neq.
    constructor; eauto.
  move=> x A B s nA ihA nB ihB xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A B s nA ihA nB ihB xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A m s nA ihA nM ihM xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihM. exact: n_ren_up.
  move=> x A Cs s nA ihA nCs ihCs xi n.
    constructor.
    apply: ihA...
    elim: ihCs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'. apply n_ren_up...
    asimpl in ih...
  move=> x m Q Fs nM ihM nQ ihQ nFs ihFs xi n.
    constructor.
    apply: ihM...
    apply: ihQ...
    elim: ihFs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'...
    asimpl in ih...
  move=> x m Q Fs nM ihM nQ ihQ nFs ihFs xi n.
    constructor.
    apply: ihM...
    apply: ihQ...
    elim: ihFs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'...
    asimpl in ih...
  move=> x A m nA ihA nM ihM xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihM...
Qed.

Lemma noccurs_ren_Forall x ms xi :
  List.Forall (noccurs x) ms -> n_ren xi x ->
    List.Forall (noccurs x) ms..[ren xi].
Proof.
  move=> no. elim: no xi=>//={ms}.
  move=> m ms nM nMs ih xi n.
    constructor.
    apply: noccurs_ren; eauto.
    apply: ih; eauto.
Qed.

Lemma pos_ren x A xi :
  pos x A -> n_ren xi x -> pos x A.[ren xi].
Proof.
  move=> p. elim: p xi=>{x A}//=.
  move=> x ms no xi [e h].
    rewrite spine_subst=>//=.
    rewrite e. constructor. exact: noccurs_ren_Forall.
  move=> x A B s nA pB ihB xi n.
    constructor.
    exact: noccurs_ren.
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A B s nA pB ihB xi n.
    constructor.
    exact: noccurs_ren.
    asimpl. apply: ihB. exact: n_ren_up.
Qed.

Lemma active_ren i C xi :
  active i C -> n_ren xi i -> active i C.[ren xi].
Proof.
  move=> c. elim: c xi=>{i C}//=.
  move=> x ms no xi [e h].
    rewrite spine_subst; asimpl.
    rewrite e.
    apply: active_X.
    elim: no=>//=.
    move{ms}=> m ms nM nMs ihMs.
      constructor; asimpl.
      apply: noccurs_ren; eauto; constructor; eauto.
      exact: ihMs.
  move=> x A B s pA c ih nB xi n.
    apply: active_Pos.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. exact: n_ren0.
  move=> x A B s nA c ih xi n.
    apply: active_Lolli.
    apply: noccurs_ren; eauto.
    asimpl. apply: ih. exact: n_ren_up.
Qed.  

Lemma constr_ren i s C xi :
  constr i s C -> n_ren xi i -> constr i s C.[ren xi].
Proof.
  move=> c. elim: c xi=>{i s C}.
  move=> x s ms no xi [e h].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no=>//=.
    move{ms}=> m ms nM nMs ihMs.
      constructor.
      apply: noccurs_ren; eauto; constructor; eauto.
      apply: ihMs.
  move=> x A B pA c ih nB xi n=>//=.
    apply: constr_UPos.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. apply n_ren0.
  move=> x A B nA cB ih xi n=>//=.
    apply: constr_UProd.
    apply: noccurs_ren; eauto.
    asimpl. apply: ih. exact: n_ren_up.
  move=> x A B pA cB ih no xi n=>//=.
    apply: constr_LPos1.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. apply n_ren0.
  move=> x A B pA c nB xi n=>//=.
    apply: constr_LPos2.
    exact: pos_ren.
    asimpl. apply: active_ren; eauto. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. exact: n_ren0.
  move=> x A B nA c ih xi n=>//=.
    apply: constr_LProd1.
    exact: noccurs_ren.
    asimpl. apply: ih. exact: n_ren_up.
  move=> x A B nA c xi n=>//=.
    apply: constr_LProd2.
    exact: noccurs_ren.
    asimpl. apply: active_ren; eauto. exact: n_ren_up.
Qed.

Lemma drespine_respine I :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall Q, respine Q I = Q).
Proof.
  elim: I=>//=.
  move=> A _ B _ s h Q.
    move: (h Q (Var 0))=>//=.
  move=> A _ B _ s h Q.
    move: (h (Lam Q Q s) (Var 0))=>//=.
  move=> m _ n _ h Q.
    move: (h (Lam Q Q U) (Var 0))=>//=.
Qed.

Lemma respine_ren1 (I : var -> term) :
  (forall i Q, respine Q (I i) = Q) ->
  (forall i Q, respine Q (I i).[ren (+1)] = Q).
Proof.
  move=> h i.
  move e:(I i)=> n.
  elim: n e h=>//=.
  move=> A _ B _ s e h Q.
    move: (h i (Var 0)).
    by rewrite e=>//=.
  move=> A _ B _ s e h Q.
    move: (h i (Var 0)).
    by rewrite e=>//=.
  move=> m _ n _ e h Q.
    move: (h i (Var 0)).
    by rewrite e=>//=.
Qed.

Lemma drespine_ren1 (I : var -> term) :
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (forall i c Q, drespine Q c (I i).[ren (+1)] = App Q c).
Proof.
  move=> h i.
  move e:(I i)=> n.
  elim: n e h=>//=.
  move=> A _ B _ s e h c Q.
    move: (h i c (Var 0)).
    by rewrite e=>//=.
  move=> A _ B _ s e h c Q.
    move: (h i c (Var 0)).
    by rewrite e=>//=.
  move=> m _ n _ e h c Q.
    move: (h i c (Var 0)).
    by rewrite e=>//=.
Qed.

Lemma respine_up I :
  (forall i Q, respine Q (I i) = Q) ->
  (forall i Q, respine Q (up I i) = Q).
Proof.
  move=> h i.
  elim: i I h=>//=.
  move=> i ih I h Q; asimpl.
  by apply respine_ren1.
Qed.

Lemma drespine_up I :
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (forall i c Q, drespine Q c (up I i) = App Q c).
Proof.
  move=> h i.
  elim: i I h=>//=.
  move=> i ih I h c Q; asimpl.
  by apply drespine_ren1.
Qed.

Lemma arity1_ren s s' A xi : 
  arity s A -> (arity1 s' A).[ren xi] = arity1 s' A.[ren xi].
Proof.
  move=> ar. elim: ar xi s'=>{A}//=.
  move=> A B ar ih xi s'; asimpl.
  rewrite ih; eauto.
Qed.

Lemma arity2_ren s s' I A xi : 
  arity s A -> (arity2 s' I A).[ren xi] = arity2 s' I.[ren xi] A.[ren xi].
Proof.
  move=> ar. elim: ar I xi s'=>{A}//=.
  move=> A B ar ih I xi s'; asimpl.
  rewrite ih; asimpl; eauto.
Qed.

Lemma respine_I_ren Q I xi :
  (forall Q, respine Q I = Q) ->
  Q.[ren xi] = respine Q.[ren xi] I.[ren xi].
Proof.
  elim: I xi Q=>//=.
  move=> A _ B _ s xi Q h.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s xi Q h.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi Q h.
    move: (h (Var 0))=>//=.
Qed.

Lemma drespine_I_ren Q c I xi :
  (forall Q, drespine Q c I = App Q c) ->
  App Q.[ren xi] c.[ren xi] = drespine Q.[ren xi] c.[ren xi] I.[ren xi].
Proof.
  elim: I xi c Q=>//=.
  move=> A _ B _ s xi c Q h.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s xi c Q h.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi c Q h.
    move: (h (Var 0))=>//=.
Qed.

Lemma respine_spine'_I_ren Q I ms xi :
  (forall Q, respine Q I = Q) ->
  (respine Q (spine' I ms)).[ren xi] =
    respine Q.[ren xi] (spine' I ms).[ren xi].
Proof.
  elim: ms Q I xi=>//=.
  move=> Q I xi h.
    rewrite h.
    by apply respine_I_ren.
  move=> m ms ih Q I xi h.
    rewrite ih; eauto.
Qed.

Lemma drespine_spine'_I_ren Q c I ms xi :
  (forall Q c, drespine Q c I = App Q c) ->
  (drespine Q c (spine' I ms)).[ren xi] =
    drespine Q.[ren xi] c.[ren xi] (spine' I ms).[ren xi].
Proof.
  elim: ms Q c I xi=>//=.
  move=> Q c I xi h.
    rewrite h.
    by apply drespine_I_ren.
  move=> m ms ih Q c I xi h.
    repeat f_equal.
    apply respine_spine'_I_ren.
    by apply drespine_respine.
Qed.

Lemma respine_spine_I_ren Q I ms xi :
  (forall Q, respine Q I = Q) ->
  (respine Q (spine I ms)).[ren xi] =
    respine Q.[ren xi] (spine I ms).[ren xi].
Proof.
  move=> h.
  rewrite spine_spine'_rev.
  by rewrite respine_spine'_I_ren.
Qed.

Lemma drespine_spine_I_ren Q c I ms xi :
  (forall Q c, drespine Q c I = App Q c) ->
  (drespine Q c (spine I ms)).[ren xi] =
    drespine Q.[ren xi] c.[ren xi] (spine I ms).[ren xi].
Proof.
  move=> h.
  rewrite spine_spine'_rev.
  by rewrite drespine_spine'_I_ren.
Qed.

Lemma active_respine_ren n (Q C : term) I (xi : var -> var) :
  active n C ->
  (forall i Q, respine Q (I i) = Q) ->
  (respine Q C.[I]).[ren xi] = 
    respine Q.[ren xi] C.[I].[ren xi].
Proof.
  move=> c; unfold case.
  elim: c Q I xi; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
Qed.

Lemma active_drespine_ren n (Q c C : term) I (xi : var -> var) :
  active n C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (drespine Q c C.[I]).[ren xi] = 
    drespine Q.[ren xi] c.[ren xi] C.[I].[ren xi].
Proof.
  move=> a; unfold case.
  elim: a c Q I xi; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. repeat f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    apply: respine_up=> i.
    by apply: drespine_respine.
  - asimpl. repeat f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    apply: respine_up=> i.
    by apply: drespine_respine.
Qed.

Lemma constr_respine_ren n s (Q C : term) I (xi : var -> var) :
  constr n s C ->
  (forall i Q, respine Q (I i) = Q) ->
  (respine Q C.[I]).[ren xi] = 
    respine Q.[ren xi] C.[I].[ren xi].
Proof.
  move=> c; unfold case.
  elim: c Q I xi; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    by apply respine_up.
Qed.

Lemma constr_drespine_ren n s (Q c C : term) I (xi : var -> var) :
  constr n s C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (drespine Q c C.[I]).[ren xi] = 
    drespine Q.[ren xi] c.[ren xi] C.[I].[ren xi].
Proof.
  move=> cn; unfold case.
  elim: cn Q c I xi; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    erewrite active_drespine_ren; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    erewrite active_drespine_ren; asimpl; eauto.
    by apply drespine_up.
Qed.

Lemma All2_case_ren Gamma Gamma' s A Q Fs Cs Cs' xi :
  All2 (fun F C =>
    constr 0 s C /\
    forall Gamma' xi, agree_ren xi Gamma Gamma' ->
      [ Gamma' |- F.[ren xi] :- (case (Ind A Cs' s) Q C).[ren xi] ])
    Fs Cs ->
  agree_ren xi Gamma Gamma' ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Gamma' |- F :- case (Ind A.[ren xi] Cs'..[up (ren xi)] s) Q.[ren xi] C])
    Fs..[ren xi] Cs..[up (ren xi)].
Proof.
  elim: Fs Gamma Gamma' s A Q Cs xi.
  move=> Gamma Gamma' s A Q Cs xi h. inv h=> *.
    constructor.
  move=> F Fs ih Gamma Gamma' s A Q Cs xi h ag.
  destruct Cs; inv h. inv H2; asimpl.
  constructor. split.
  - apply: constr_ren; eauto.
    apply: n_ren0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold case in H0.
    erewrite constr_respine_ren in H0; eauto.
    asimpl in H0.
    by unfold case; asimpl.
    move=> i Q'.
    destruct i; asimpl; eauto.
  - replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih; eauto.
Qed.

Lemma All2i_case_ren Gamma Gamma' n s A Q Fs Cs Cs' xi :
  All2i (fun i F C =>
    let I := Ind A Cs' s in
    constr 0 s C /\
    forall Gamma' xi, agree_ren xi Gamma Gamma' ->
      [ Gamma' |- F.[ren xi] :- (dcase I Q (Constr i I) C).[ren xi] ])
    n Fs Cs ->
  agree_ren xi Gamma Gamma' ->
  All2i (fun i F C =>
    let I := Ind A.[ren xi] Cs'..[up (ren xi)] s in
    constr 0 s C /\
    [ Gamma' |- F :- dcase I Q.[ren xi] (Constr i I) C])
    n Fs..[ren xi] Cs..[up (ren xi)].
Proof.
  elim: Fs Gamma Gamma' n s A Q Cs xi.
  move=> Gamma Gamma' n s A Q Cs xi h. inv h=> *.
    constructor.
  move=> F Fs ih Gamma Gamma' n s A Q Cs xi h ag.
  destruct Cs; inv h. inv H3; asimpl.
  constructor. split.
  - apply: constr_ren; eauto.
    apply: n_ren0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold dcase in H0.
    erewrite constr_drespine_ren in H0; eauto.
    asimpl in H0.
    by unfold dcase; asimpl.
    move=> i Q'.
    destruct i; asimpl; eauto.
  - replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih; eauto.
Qed.

Lemma rename_ok Gamma Gamma' m A xi :
  [ Gamma |- m :- A ] ->
  agree_ren xi Gamma Gamma' ->
  [ Gamma' |- m.[ren xi] :- A.[ren xi] ].
Proof with eauto using agree_ren, agree_ren_pure, agree_ren_re_re.
  move=> ty.
  move: Gamma m A ty Gamma' xi.
  apply: has_type_nested_ind=> //=.
  move=> Gamma s l pu Gamma' xi ag.
    apply: u_Sort...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: u_Prod...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: l_Prod...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: u_Lolli...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: l_Lolli...
  move=> Gamma x A hs Gamma' xi ag //=.
    apply: u_Var.
    apply: agree_ren_hasU...
  move=> Gamma x A hs Gamma' xi ag //=.
    apply: l_Var.
    apply: agree_ren_hasL...
  move=> Gamma n A B s t l pu ty1 ih1 ty2 ih2 Gamma' xi ag.
    apply: u_Lam...
    asimpl. apply: ih2. destruct s; constructor...
  move=> Gamma n A B s t l ty1 ih1 ty2 ih2 Gamma' xi ag.
    apply: l_Lam.
    apply: ih1. apply: agree_ren_re_re...
    asimpl. apply: ih2. destruct s; constructor...
  move=> Gamma1 Gamma2 Gamma A B m n pu ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    move: (agree_ren_pure ag2 pu)=> {} pu.
    apply: u_Prod_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma1 Gamma2 Gamma A B m n ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    apply: l_Prod_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma1 Gamma2 Gamma A B m n pu ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    move: (agree_ren_pure ag2 pu)=> {} pu.
    apply: u_Lolli_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma1 Gamma2 Gamma A B m n ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    apply: l_Lolli_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma A s Cs l ar cnstr pu ty1 ih1 ty2 ih2 Gamma' xi ag.
    apply: s_Ind...
    exact: arity_ren.
    move=>{ag}. elim: cnstr xi=>//=...
      move=> m ms c hMs ihMs xi; asimpl.
      constructor. 
      apply: constr_ren... apply: n_ren0.
      move: (ihMs xi)=> {} ihMs.
      asimpl in ihMs. exact: ihMs.
    elim: ih2=>//=.
      move=> m ms ihM hMs ihMs; asimpl.
      constructor. 
      asimpl. apply: ihM...
      asimpl in ihMs. exact: ihMs.
  move=> Gamma A s i C Cs ig pu ty ih Gamma' xi ag.
    replace (C.[Ind A Cs s/].[ren xi]) 
      with (C.[up (ren xi)]).[Ind A.[ren xi] Cs..[up (ren xi)] s/]
        by autosubst.
    apply: s_Constr...
    apply: iget_subst...
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms ar mg 
    tyM ihM tyQ ihQ ty ih Gamma' xi ag.
    rewrite spine_subst.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    move: (arity_ren xi ar)=> ar'.
    move: (agree_ren_re_re ag2)=> rag2.
    move: (ihM _ _ ag1)=> {} ihM. rewrite spine_subst in ihM.
    move: (ihQ _ _ rag2)=> {} ihQ.
    move: (arity1_ren s' xi ar)=> e. rewrite e in ihQ.
    apply: s_Case...
    apply: All2_case_ren...
  move=> Gamma1 Gamma2 Gamma A Q s Fs Cs m ms ar p mg
    tyM ihM tyQ ihQ ty ih Gamma' xi ag.
    rewrite spine_subst.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    move: (arity_ren xi ar)=> ar'.
    move: (agree_ren_re_re ag2)=> rag2.
    move: (ihM _ _ ag1)=> {} ihM. rewrite spine_subst in ihM.
    move: (ihQ _ _ rag2)=> {} ihQ.
    move: (arity2_ren s (Ind A Cs U) xi ar)=> e. rewrite e in ihQ.
    move: (agree_ren_pure ag1 p)=>{}p.
    apply: s_DCase...
    apply: All2i_case_ren...
  move=> Gamma A m l p tyA ihA tyM ihM Gamma' xi ag.
    econstructor...
    have ag' : agree_ren (upren xi) (A +u Gamma) (A.[ren xi] +u Gamma').
      by constructor.
    move: (ihM _ _ ag'); asimpl=>//.
  move=> Gamma A B m s l sub tyB ihB tyM ihM Gamma' xi ag.
    apply: s_Conv.
    apply: sub_ren.
    apply: sub.
    apply: ihB.
    by apply: agree_ren_re_re.
    by apply: ihM.
Qed.

Lemma hasU_ok Gamma x A :
  [ Gamma |- ] ->
  hasU Gamma x A ->
  exists l, [ re Gamma |- A :- Sort U l ].
Proof.
  move=> wf. elim: wf x A.
  move=> x A h. inv h.
  move=> Gamma' A l wf ih tyA x A' h. inv h=>//=.
    exists l.
    replace (Sort U l) with (Sort U l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
    move: (ih _ _ H3)=>{ih}[l' tyM].
    exists l'.
    replace (Sort U l') with (Sort U l').[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
  move=> Gamma' A l wf ih tyA x A' h. inv h.
  move=> Gamma' wf ih x A h. inv h=>//=.
    move: (ih _ _ H0)=>{ih}[l tyM].
    exists l.
    replace (Sort U l) with (Sort U l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
Qed.

Lemma hasL_ok Gamma x A :
  [ Gamma |- ] ->
  hasL Gamma x A ->
  exists l, [ re Gamma |- A :- Sort L l ].
Proof.
  move=> wf. elim: wf x A.
  move=> x A h. inv h.
  move=> Gamma' A l wf ih tyA x A' h=>//=. inv h.
    move: (ih _ _ H3)=>{ih}[l' tyM].
    exists l'.
    replace (Sort L l') with (Sort L l').[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
  move=> Gamma' A l wf ih tyA x A' h=>//=. inv h.
    exists l.
    replace (Sort L l) with (Sort L l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
  move=> Gamma' wf ih x A h=>//=. inv h.
    move: (ih _ _ H0)=>{ih}[l tyM].
    exists l.
    replace (Sort L l) with (Sort L l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
Qed.

Lemma weakeningU Gamma m A B :
  [ Gamma |- m :- A ] ->
  [ B +u Gamma |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> tyM.
  apply: rename_ok; eauto.
  apply: agree_ren_wkU.
  apply: agree_ren_refl.
Qed.

Lemma weakeningN Gamma m A :
  [ Gamma |- m :- A ] ->
  [ +n Gamma |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> tyM.
  apply: rename_ok; eauto.
  apply: agree_ren_wkN.
  apply: agree_ren_refl.
Qed.

Lemma eweakeningU Gamma m m' A A' B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A ] -> 
  [ B +u Gamma |- m' :- A' ].
Proof.
  move=>->-> h.  
  apply: weakeningU; eauto.
Qed.

Lemma eweakeningN Gamma m m' A A' :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A ] -> 
  [ +n Gamma |-m' :- A' ].
Proof.
  move=>->-> h.
  apply: weakeningN; eauto.
Qed.