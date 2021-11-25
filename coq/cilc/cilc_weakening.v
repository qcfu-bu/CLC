From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_u Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m +u Γ) (m.[ren ξ] +u Γ')
| agree_ren_l Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m +l Γ) (m.[ren ξ] +l Γ')
| agree_ren_n Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (+n Γ) (+n Γ')
| agree_ren_wkU Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) Γ (m +u Γ')
| agree_ren_wkN Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) Γ (+n Γ').

Lemma agree_ren_refl Γ : agree_ren id Γ Γ.
Proof.
  elim: Γ.
  apply: agree_ren_nil.
  move=> a Γ ag.
  destruct a.
  destruct p.
  destruct s.
  have h : (agree_ren id (t +u Γ) (t +u Γ)
    = agree_ren (upren id) (t +u Γ) (t.[ren id] +u Γ))
    by autosubst.
  rewrite h; constructor; eauto.
  have h : (agree_ren id (t +l Γ) (t +l Γ)
    = agree_ren (upren id) (t +l Γ) (t.[ren id] +l Γ))
    by autosubst.
  rewrite h; constructor; eauto.
  have h : (agree_ren id (+n Γ) (+n Γ)
    = agree_ren (upren id) (+n Γ) (+n Γ))
    by autosubst.
  rewrite h; constructor; eauto.
Qed.

Lemma agree_ren_pure Γ Γ' ξ :
  agree_ren ξ Γ Γ' -> pure Γ -> pure Γ'.
Proof with eauto using pure.
  elim=>{Γ Γ' ξ} //=...
  move=> Γ Γ' ξ m ag ih pu.
    inv pu...
  move=> Γ Γ' ξ m ag ih pu.
    inv pu.
  move=> Γ Γ' ξ ag ih pu.
    inv pu...
Qed.

Lemma agree_ren_re_re Γ Γ' ξ :
  agree_ren ξ Γ Γ' -> agree_ren ξ (re Γ) (re Γ').
Proof. elim; eauto using agree_ren. Qed.

Lemma agree_ren_hasU Γ Γ' ξ x A :
  agree_ren ξ Γ Γ' ->
  hasU Γ x A ->
  hasU Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=> ag. elim: ag x A=> {Γ Γ' ξ}.
  move=> ξ x A hs. inv hs.
  move=> Γ Γ' ξ m ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_ren_pure...
    replace (m0.[ren (+1)].[ren (upren ξ)]) 
      with (m0.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Γ Γ' ξ m ag ih x A hs. inv hs.
  move=> Γ Γ' ξ ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Γ Γ' ξ m ag ih x A hs.
    replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Γ Γ' ξ ag ih x A hs.
    replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
Qed.

Lemma agree_ren_hasL Γ Γ' ξ x A :
  agree_ren ξ Γ Γ' ->
  hasL Γ x A ->
  hasL Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=> ag. elim: ag x A=>{Γ Γ' ξ}.
  move=> ξ x A hs. inv hs.
  move=> Γ Γ' ξ m ag ih x A hs. inv hs.
    replace (m0.[ren (+1)].[ren (upren ξ)]) 
      with (m0.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Γ Γ' ξ m ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_ren_pure...
  move=> Γ Γ' ξ ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren ξ)]) 
      with (m.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Γ Γ' ξ m ag ih x A hs.
    replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Γ Γ' ξ ag ih x A hs.
    replace (A.[ren ((+1) ∘ ξ)])
      with (A.[ren ξ].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
Qed.

Lemma merge_agree_ren_inv Γ1 Γ2 Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
    merge Γ1 Γ2 Γ ->
    exists Γ1' Γ2',
      merge Γ1' Γ2' Γ' /\
      agree_ren ξ Γ1 Γ1' /\
      agree_ren ξ Γ2 Γ2'.
Proof with eauto.
  move=> ag. elim: ag Γ1 Γ2=>{Γ Γ' ξ}.
  move=> ξ Γ1 Γ2 mg. inv mg.
    exists nil. exists nil. repeat constructor.
  move=> Γ Γ' ξ m ag ih Γ1 Γ2 mg. inv mg.
    move: H2=>/ih[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    exists (m.[ren ξ] +u Γ1').
    exists (m.[ren ξ] +u Γ2').
    repeat constructor...
  move=> Γ Γ' ξ m ag ih Γ1 Γ2 mg. inv mg.
    move: H2=>/ih[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    exists (m.[ren ξ] +l Γ1').
    exists (+n Γ2').
      repeat constructor...
    move: H2=>/ih[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    exists (+n Γ1').
    exists (m.[ren ξ] +l Γ2').
      repeat constructor...
  move=> Γ Γ' ξ ag ih Γ1 Γ2 mg. inv mg.
    move: H2=>/ih[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    exists (+n Γ1').
    exists (+n Γ2').
    repeat constructor...
  move=> Γ Γ' ξ m ag ih Γ1 Γ2 mg.
    move: mg=>/ih[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    exists (m +u Γ1').
    exists (m +u Γ2').
    repeat constructor...
  move=> Γ Γ' ξ ag ih Γ1 Γ2 mg.
    move: mg=>/ih[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    exists (+n Γ1').
    exists (+n Γ2').
    repeat constructor...
Qed.

Lemma arity_ren s A ξ : arity s A -> arity s A.[ren ξ].
Proof with eauto using arity.
  move=> ar. elim: ar ξ=>//=...
  move=> A' B ar ih ξ.
    constructor.
    replace (up (ren ξ)) with (ren (upren ξ)) by autosubst.
    exact: ih.
Qed.

Definition n_ren (ξ : var -> var) x :=
  ξ x = x /\ 
    forall i, (~x = i -> ~ξ i = x) /\ (~i = 0 -> ~ξ i = 0).

Lemma n_ren0 ξ : n_ren (upren ξ) 0.
Proof.
  split; eauto.
  move=> i. elim: i ξ=>//=.
Qed.

Lemma n_ren_up ξ x :
  n_ren ξ x -> n_ren (upren ξ) x.+1.
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

Lemma noccurs_ren x m ξ :
  noccurs x m -> n_ren ξ x -> noccurs x m.[ren ξ].
Proof with eauto using noccurs, n_ren_up, and.
  move=> no. move: x m no ξ.
  apply: noccurs_ind_nested=>//=...
  move=> x y neq ξ [e h].
    move: (h y)=> {h} [h _].
    move: neq=> /h neq.
    constructor; eauto.
  move=> x A B s nA ihA nB ihB ξ n.
    constructor.
    apply: ihA...
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A B s nA ihA nB ihB ξ n.
    constructor.
    apply: ihA...
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A m s nA ihA nM ihM ξ n.
    constructor.
    apply: ihA...
    asimpl. apply: ihM. exact: n_ren_up.
  move=> x A Cs s nA ihA nCs ihCs ξ n.
    constructor.
    apply: ihA...
    elim: ihCs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'. apply n_ren_up...
    asimpl in ih...
  move=> x m Q Fs nM ihM nQ ihQ nFs ihFs ξ n.
    constructor.
    apply: ihM...
    apply: ihQ...
    elim: ihFs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'...
    asimpl in ih...
  move=> x m Q Fs nM ihM nQ ihQ nFs ihFs ξ n.
    constructor.
    apply: ihM...
    apply: ihQ...
    elim: ihFs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'...
    asimpl in ih...
  move=> x A m nA ihA nM ihM ξ n.
    constructor.
    apply: ihA...
    asimpl. apply: ihM...
Qed.

Lemma noccurs_ren_Forall x ms ξ :
  List.Forall (noccurs x) ms -> n_ren ξ x ->
    List.Forall (noccurs x) ms..[ren ξ].
Proof.
  move=> no. elim: no ξ=>//={ms}.
  move=> m ms nM nMs ih ξ n.
    constructor.
    apply: noccurs_ren; eauto.
    apply: ih; eauto.
Qed.

Lemma pos_ren x A ξ :
  pos x A -> n_ren ξ x -> pos x A.[ren ξ].
Proof.
  move=> p. elim: p ξ=>{x A}//=.
  move=> x ms no ξ [e h].
    rewrite spine_subst=>//=.
    rewrite e. constructor. exact: noccurs_ren_Forall.
  move=> x A B s nA pB ihB ξ n.
    constructor.
    exact: noccurs_ren.
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A B s nA pB ihB ξ n.
    constructor.
    exact: noccurs_ren.
    asimpl. apply: ihB. exact: n_ren_up.
Qed.

Lemma active_ren i C ξ :
  active i C -> n_ren ξ i -> active i C.[ren ξ].
Proof.
  move=> c. elim: c ξ=>{i C}//=.
  move=> x ms no ξ [e h].
    rewrite spine_subst; asimpl.
    rewrite e.
    apply: active_X.
    elim: no=>//=.
    move{ms}=> m ms nM nMs ihMs.
      constructor; asimpl.
      apply: noccurs_ren; eauto; constructor; eauto.
      exact: ihMs.
  move=> x A B s pA c ih nB ξ n.
    apply: active_Pos.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. exact: n_ren0.
  move=> x A B s nA c ih ξ n.
    apply: active_Lolli.
    apply: noccurs_ren; eauto.
    asimpl. apply: ih. exact: n_ren_up.
Qed.  

Lemma constr_ren i s C ξ :
  constr i s C -> n_ren ξ i -> constr i s C.[ren ξ].
Proof.
  move=> c. elim: c ξ=>{i s C}.
  move=> x s ms no ξ [e h].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no=>//=.
    move{ms}=> m ms nM nMs ihMs.
      constructor.
      apply: noccurs_ren; eauto; constructor; eauto.
      apply: ihMs.
  move=> x A B pA c ih nB ξ n=>//=.
    apply: constr_UPos.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. apply n_ren0.
  move=> x A B nA cB ih ξ n=>//=.
    apply: constr_UProd.
    apply: noccurs_ren; eauto.
    asimpl. apply: ih. exact: n_ren_up.
  move=> x A B pA cB ih no ξ n=>//=.
    apply: constr_LPos1.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. apply n_ren0.
  move=> x A B pA c nB ξ n=>//=.
    apply: constr_LPos2.
    exact: pos_ren.
    asimpl. apply: active_ren; eauto. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. exact: n_ren0.
  move=> x A B nA c ih ξ n=>//=.
    apply: constr_LProd1.
    exact: noccurs_ren.
    asimpl. apply: ih. exact: n_ren_up.
  move=> x A B nA c ξ n=>//=.
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

Lemma arity1_ren s s' A ξ : 
  arity s A -> (arity1 s' A).[ren ξ] = arity1 s' A.[ren ξ].
Proof.
  move=> ar. elim: ar ξ s'=>{A}//=.
  move=> A B ar ih ξ s'; asimpl.
  rewrite ih; eauto.
Qed.

Lemma arity2_ren s s' I A ξ : 
  arity s A -> (arity2 s' I A).[ren ξ] = arity2 s' I.[ren ξ] A.[ren ξ].
Proof.
  move=> ar. elim: ar I ξ s'=>{A}//=.
  move=> A B ar ih I ξ s'; asimpl.
  rewrite ih; asimpl; eauto.
Qed.

Lemma respine_I_ren Q I ξ :
  (forall Q, respine Q I = Q) ->
  Q.[ren ξ] = respine Q.[ren ξ] I.[ren ξ].
Proof.
  elim: I ξ Q=>//=.
  move=> A _ B _ s ξ Q h.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s ξ Q h.
    move: (h (Var 0))=>//=.
  move=> m _ n _ ξ Q h.
    move: (h (Var 0))=>//=.
Qed.

Lemma drespine_I_ren Q c I ξ :
  (forall Q, drespine Q c I = App Q c) ->
  App Q.[ren ξ] c.[ren ξ] = drespine Q.[ren ξ] c.[ren ξ] I.[ren ξ].
Proof.
  elim: I ξ c Q=>//=.
  move=> A _ B _ s ξ c Q h.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s ξ c Q h.
    move: (h (Var 0))=>//=.
  move=> m _ n _ ξ c Q h.
    move: (h (Var 0))=>//=.
Qed.

Lemma respine_spine'_I_ren Q I ms ξ :
  (forall Q, respine Q I = Q) ->
  (respine Q (spine' I ms)).[ren ξ] =
    respine Q.[ren ξ] (spine' I ms).[ren ξ].
Proof.
  elim: ms Q I ξ=>//=.
  move=> Q I ξ h.
    rewrite h.
    by apply respine_I_ren.
  move=> m ms ih Q I ξ h.
    rewrite ih; eauto.
Qed.

Lemma drespine_spine'_I_ren Q c I ms ξ :
  (forall Q c, drespine Q c I = App Q c) ->
  (drespine Q c (spine' I ms)).[ren ξ] =
    drespine Q.[ren ξ] c.[ren ξ] (spine' I ms).[ren ξ].
Proof.
  elim: ms Q c I ξ=>//=.
  move=> Q c I ξ h.
    rewrite h.
    by apply drespine_I_ren.
  move=> m ms ih Q c I ξ h.
    repeat f_equal.
    apply respine_spine'_I_ren.
    by apply drespine_respine.
Qed.

Lemma respine_spine_I_ren Q I ms ξ :
  (forall Q, respine Q I = Q) ->
  (respine Q (spine I ms)).[ren ξ] =
    respine Q.[ren ξ] (spine I ms).[ren ξ].
Proof.
  move=> h.
  rewrite spine_spine'_rev.
  by rewrite respine_spine'_I_ren.
Qed.

Lemma drespine_spine_I_ren Q c I ms ξ :
  (forall Q c, drespine Q c I = App Q c) ->
  (drespine Q c (spine I ms)).[ren ξ] =
    drespine Q.[ren ξ] c.[ren ξ] (spine I ms).[ren ξ].
Proof.
  move=> h.
  rewrite spine_spine'_rev.
  by rewrite drespine_spine'_I_ren.
Qed.

Lemma active_respine_ren n (Q C : term) I (ξ : var -> var) :
  active n C ->
  (forall i Q, respine Q (I i) = Q) ->
  (respine Q C.[I]).[ren ξ] = 
    respine Q.[ren ξ] C.[I].[ren ξ].
Proof.
  move=> c; unfold case.
  elim: c Q I ξ; intros.
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

Lemma active_drespine_ren n (Q c C : term) I (ξ : var -> var) :
  active n C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (drespine Q c C.[I]).[ren ξ] = 
    drespine Q.[ren ξ] c.[ren ξ] C.[I].[ren ξ].
Proof.
  move=> a; unfold case.
  elim: a c Q I ξ; intros.
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

Lemma constr_respine_ren n s (Q C : term) I (ξ : var -> var) :
  constr n s C ->
  (forall i Q, respine Q (I i) = Q) ->
  (respine Q C.[I]).[ren ξ] = 
    respine Q.[ren ξ] C.[I].[ren ξ].
Proof.
  move=> c; unfold case.
  elim: c Q I ξ; intros.
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

Lemma constr_drespine_ren n s (Q c C : term) I (ξ : var -> var) :
  constr n s C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (drespine Q c C.[I]).[ren ξ] = 
    drespine Q.[ren ξ] c.[ren ξ] C.[I].[ren ξ].
Proof.
  move=> cn; unfold case.
  elim: cn Q c I ξ; intros.
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

Lemma All2_case_ren Γ Γ' s A Q Fs Cs Cs' ξ :
  All2 (fun F C =>
    constr 0 s C /\
    forall Γ' ξ, agree_ren ξ Γ Γ' ->
      [ Γ' |- F.[ren ξ] :- (case (Ind A Cs' s) Q C).[ren ξ] ])
    Fs Cs ->
  agree_ren ξ Γ Γ' ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Γ' |- F :- case (Ind A.[ren ξ] Cs'..[up (ren ξ)] s) Q.[ren ξ] C])
    Fs..[ren ξ] Cs..[up (ren ξ)].
Proof.
  elim: Fs Γ Γ' s A Q Cs ξ.
  move=> Γ Γ' s A Q Cs ξ h. inv h=> *.
    constructor.
  move=> F Fs ih Γ Γ' s A Q Cs ξ h ag.
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
  - replace (ren (upren ξ)) with (up (ren ξ)) by autosubst.
    apply: ih; eauto.
Qed.

Lemma All2i_case_ren Γ Γ' n s A Q Fs Cs Cs' ξ :
  All2i (fun i F C =>
    let I := Ind A Cs' s in
    constr 0 s C /\
    forall Γ' ξ, agree_ren ξ Γ Γ' ->
      [ Γ' |- F.[ren ξ] :- (dcase I Q (Constr i I) C).[ren ξ] ])
    n Fs Cs ->
  agree_ren ξ Γ Γ' ->
  All2i (fun i F C =>
    let I := Ind A.[ren ξ] Cs'..[up (ren ξ)] s in
    constr 0 s C /\
    [ Γ' |- F :- dcase I Q.[ren ξ] (Constr i I) C])
    n Fs..[ren ξ] Cs..[up (ren ξ)].
Proof.
  elim: Fs Γ Γ' n s A Q Cs ξ.
  move=> Γ Γ' n s A Q Cs ξ h. inv h=> *.
    constructor.
  move=> F Fs ih Γ Γ' n s A Q Cs ξ h ag.
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
  - replace (ren (upren ξ)) with (up (ren ξ)) by autosubst.
    apply: ih; eauto.
Qed.

Lemma rename_ok Γ Γ' m A ξ :
  [ Γ |- m :- A ] ->
  agree_ren ξ Γ Γ' ->
  [ Γ' |- m.[ren ξ] :- A.[ren ξ] ].
Proof with eauto using agree_ren, agree_ren_pure, agree_ren_re_re.
  move=> ty.
  move: Γ m A ty Γ' ξ.
  apply: has_type_nested_ind=> //=.
  move=> Γ s l pu Γ' ξ ag.
    apply: u_Sort...
  move=> Γ A B s l pu tyA ihA tyB ihB Γ' ξ ag; asimpl.
    apply: u_Prod...
  move=> Γ A B s l pu tyA ihA tyB ihB Γ' ξ ag; asimpl.
    apply: l_Prod...
  move=> Γ A B s l pu tyA ihA tyB ihB Γ' ξ ag; asimpl.
    apply: u_Lolli...
  move=> Γ A B s l pu tyA ihA tyB ihB Γ' ξ ag; asimpl.
    apply: l_Lolli...
  move=> Γ x A hs Γ' ξ ag //=.
    apply: u_Var.
    apply: agree_ren_hasU...
  move=> Γ x A hs Γ' ξ ag //=.
    apply: l_Var.
    apply: agree_ren_hasL...
  move=> Γ n A B s t l pu ty1 ih1 ty2 ih2 Γ' ξ ag.
    apply: u_Lam...
    asimpl. apply: ih2. destruct s; constructor...
  move=> Γ n A B s t l ty1 ih1 ty2 ih2 Γ' ξ ag.
    apply: l_Lam.
    apply: ih1. apply: agree_ren_re_re...
    asimpl. apply: ih2. destruct s; constructor...
  move=> Γ1 Γ2 Γ A B m n pu ty1 ih1 ty2 ih2 mg Γ' ξ ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    move: (agree_ren_pure ag2 pu)=> {} pu.
    apply: u_Prod_App...
    replace (ren (upren ξ)) with (up (ren ξ)) by autosubst.
    apply: ih1...
  move=> Γ1 Γ2 Γ A B m n ty1 ih1 ty2 ih2 mg Γ' ξ ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    apply: l_Prod_App...
    replace (ren (upren ξ)) with (up (ren ξ)) by autosubst.
    apply: ih1...
  move=> Γ1 Γ2 Γ A B m n pu ty1 ih1 ty2 ih2 mg Γ' ξ ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    move: (agree_ren_pure ag2 pu)=> {} pu.
    apply: u_Lolli_App...
    replace (ren (upren ξ)) with (up (ren ξ)) by autosubst.
    apply: ih1...
  move=> Γ1 Γ2 Γ A B m n ty1 ih1 ty2 ih2 mg Γ' ξ ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren ξ] .: ren ξ]) 
      with (B.[ren (upren ξ)].[n.[ren ξ]/]) by autosubst.
    apply: l_Lolli_App...
    replace (ren (upren ξ)) with (up (ren ξ)) by autosubst.
    apply: ih1...
  move=> Γ A s Cs l ar cnstr pu ty1 ih1 ty2 ih2 Γ' ξ ag.
    apply: s_Ind...
    exact: arity_ren.
    move=>{ag}. elim: cnstr ξ=>//=...
      move=> m ms c hMs ihMs ξ; asimpl.
      constructor. 
      apply: constr_ren... apply: n_ren0.
      move: (ihMs ξ)=> {} ihMs.
      asimpl in ihMs. exact: ihMs.
    elim: ih2=>//=.
      move=> m ms ihM hMs ihMs; asimpl.
      constructor. 
      asimpl. apply: ihM...
      asimpl in ihMs. exact: ihMs.
  move=> Γ A s i C Cs ig pu ty ih Γ' ξ ag.
    replace (C.[Ind A Cs s/].[ren ξ]) 
      with (C.[up (ren ξ)]).[Ind A.[ren ξ] Cs..[up (ren ξ)] s/]
        by autosubst.
    apply: s_Constr...
    apply: iget_subst...
  move=> Γ1 Γ2 Γ A Q s s' Fs Cs m ms ar mg 
    tyM ihM tyQ ihQ ty ih Γ' ξ ag.
    rewrite spine_subst.
    move: (merge_agree_ren_inv ag mg)=>[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    move: (arity_ren ξ ar)=> ar'.
    move: (agree_ren_re_re ag2)=> rag2.
    move: (ihM _ _ ag1)=> {} ihM. rewrite spine_subst in ihM.
    move: (ihQ _ _ rag2)=> {} ihQ.
    move: (arity1_ren s' ξ ar)=> e. rewrite e in ihQ.
    apply: s_Case...
    apply: All2_case_ren...
  move=> Γ1 Γ2 Γ A Q s Fs Cs m ms ar p mg
    tyM ihM tyQ ihQ ty ih Γ' ξ ag.
    rewrite spine_subst.
    move: (merge_agree_ren_inv ag mg)=>[Γ1'[Γ2'[mg'[ag1 ag2]]]].
    move: (arity_ren ξ ar)=> ar'.
    move: (agree_ren_re_re ag2)=> rag2.
    move: (ihM _ _ ag1)=> {} ihM. rewrite spine_subst in ihM.
    move: (ihQ _ _ rag2)=> {} ihQ.
    move: (arity2_ren s (Ind A Cs U) ξ ar)=> e. rewrite e in ihQ.
    move: (agree_ren_pure ag1 p)=>{}p.
    apply: s_DCase...
    apply: All2i_case_ren...
  move=> Γ A m l p tyA ihA tyM ihM Γ' ξ ag.
    econstructor...
    have ag' : agree_ren (upren ξ) (A +u Γ) (A.[ren ξ] +u Γ').
      by constructor.
    move: (ihM _ _ ag'); asimpl=>//.
  move=> Γ A B m s l sub tyB ihB tyM ihM Γ' ξ ag.
    apply: s_Conv.
    apply: sub_ren.
    apply: sub.
    apply: ihB.
    by apply: agree_ren_re_re.
    by apply: ihM.
Qed.

Lemma hasU_ok Γ x A :
  [ Γ |- ] ->
  hasU Γ x A ->
  exists l, [ re Γ |- A :- Sort U l ].
Proof.
  move=> wf. elim: wf x A.
  move=> x A h. inv h.
  move=> Γ' A l wf ih tyA x A' h. inv h=>//=.
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
  move=> Γ' A l wf ih tyA x A' h. inv h.
  move=> Γ' wf ih x A h. inv h=>//=.
    move: (ih _ _ H0)=>{ih}[l tyM].
    exists l.
    replace (Sort U l) with (Sort U l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
Qed.

Lemma hasL_ok Γ x A :
  [ Γ |- ] ->
  hasL Γ x A ->
  exists l, [ re Γ |- A :- Sort L l ].
Proof.
  move=> wf. elim: wf x A.
  move=> x A h. inv h.
  move=> Γ' A l wf ih tyA x A' h=>//=. inv h.
    move: (ih _ _ H3)=>{ih}[l' tyM].
    exists l'.
    replace (Sort L l') with (Sort L l').[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
  move=> Γ' A l wf ih tyA x A' h=>//=. inv h.
    exists l.
    replace (Sort L l) with (Sort L l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
  move=> Γ' wf ih x A h=>//=. inv h.
    move: (ih _ _ H0)=>{ih}[l tyM].
    exists l.
    replace (Sort L l) with (Sort L l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
Qed.

Lemma weakeningU Γ m A B :
  [ Γ |- m :- A ] ->
  [ B +u Γ |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> tyM.
  apply: rename_ok; eauto.
  apply: agree_ren_wkU.
  apply: agree_ren_refl.
Qed.

Lemma weakeningN Γ m A :
  [ Γ |- m :- A ] ->
  [ +n Γ |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> tyM.
  apply: rename_ok; eauto.
  apply: agree_ren_wkN.
  apply: agree_ren_refl.
Qed.

Lemma eweakeningU Γ m m' A A' B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Γ |- m :- A ] -> 
  [ B +u Γ |- m' :- A' ].
Proof.
  move=>->-> h.  
  apply: weakeningU; eauto.
Qed.

Lemma eweakeningN Γ m m' A A' :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Γ |- m :- A ] -> 
  [ +n Γ |-m' :- A' ].
Proof.
  move=>->-> h.
  apply: weakeningN; eauto.
Qed.