From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context clc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive All2 R : list term -> list term -> Prop :=
| All2_nil : All2 R nil nil
| All2_cons m m' ls ls' :
  R m m' ->
  All2 R ls ls' ->
  All2 R (m :: ls) (m' :: ls').

Inductive All2i R : nat -> list term -> list term -> Prop :=
| All2i_nil i : All2i R i nil nil
| All2i_cons i m m' ls ls' :
  R i m m' ->
  All2i R i.+1 ls ls' ->
  All2i R i (m :: ls) (m' :: ls').

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort s l :
  pstep (s @ l) (s @ l)
| pstep_lam A A' n n' s t : 
  pstep A A' -> 
  pstep n n' -> 
  pstep (Lam A n s t) (Lam A' n' s t)
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta A m m' n n' s t :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam A m s t) n) (m'.[n'/])
| pstep_pi A A' B B' s r t :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi A B s r t) 
        (Pi A' B' s r t)
| pstep_indd A A' Cs Cs' s :
  pstep A A' ->
  All2 pstep Cs Cs' ->
  pstep (Ind A Cs s) (Ind A' Cs' s)
| pstep_constr i m m' :
  pstep m m' ->
  pstep (Constr i m) (Constr i m')
| pstep_case m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  All2 pstep Fs Fs' ->
  pstep (Case m Q Fs) (Case m' Q' Fs')
| pstep_iota1 i m ms ms' Q Fs Fs' F' :
  iget i Fs' F' ->
  All2 pstep ms ms' ->
  All2 pstep Fs Fs' ->
  pstep (Case (spine (Constr i m) ms) Q Fs) (spine F' ms')
| pstep_fix A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fix A m) (Fix A' m')
| pstep_iota2 A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fix A m) (m'.[Fix A' m'/]).

Section pstep_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_var : forall x, P (Var x) (Var x).
  Hypothesis ih_sort : forall s l, P (Sort s l) (Sort s l).
  Hypothesis ih_lam :
    forall A A' n n' s t, pstep A A' -> P A A' -> pstep n n' -> P n n' ->
      P (Lam A n s t) (Lam A' n' s t).
  Hypothesis ih_app :
    forall m m' n n', pstep m m' -> P m m' -> pstep n n' -> P n n' ->
      P (App m n) (App m' n').
  Hypothesis ih_beta :
    forall A m m' n n' s t, pstep m m' -> P m m' -> pstep n n' -> P n n' ->
      P (App (Lam A m s t) n) m'.[n'/].
  Hypothesis ih_pi :
    forall A A' B B' s r t, pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Pi A B s r t) (Pi A' B' s r t).
  Hypothesis ih_indd :
    forall A A' Cs Cs' s, pstep A A' -> P A A' -> All2 pstep Cs Cs' -> All2 P Cs Cs' ->
      P (Ind A Cs s) (Ind A' Cs' s).
  Hypothesis ih_constr :
    forall i m m', pstep m m' -> P m m' -> P (Constr i m) (Constr i m').
  Hypothesis ih_case :
    forall m m' Q Q' Fs Fs',
      pstep m m' -> P m m' ->
      pstep Q Q' -> P Q Q' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (Case m Q Fs) (Case m' Q' Fs').
  Hypothesis ih_iota1 :
    forall i m ms ms' Q Fs Fs' F',
      iget i Fs' F' ->
      All2 pstep ms ms' -> All2 P ms ms' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (Case (spine (Constr i m) ms) Q Fs) (spine F' ms').
  Hypothesis ih_fix :
    forall A A' m m', pstep A A' -> P A A' -> pstep m m' -> P m m' ->
      P (Fix A m) (Fix A' m').
  Hypothesis ih_iota2 :
    forall A A' m m', pstep A A' -> P A A' -> pstep m m' -> P m m' ->
      P (Fix A m) (m'.[Fix A' m'/]).

  Fixpoint pstep_ind_nested m m' (st : pstep m m') : P m m'.
  Proof.
    have ih_nested :=
      fix fold ls1 ls2 (p : All2 pstep ls1 ls2) : All2 P ls1 ls2 :=
        match p with
        | All2_nil => All2_nil _
        | All2_cons _ _ _ _ hd tl =>
          All2_cons (pstep_ind_nested _ _ hd) (fold _ _ tl)
        end.
    case st; move=>*.
    apply: ih_var.
    apply: ih_sort.
    apply: ih_lam; eauto.
    apply: ih_app; eauto.
    apply: ih_beta; eauto.
    apply: ih_pi; eauto.
    apply: ih_indd; eauto.
    apply: ih_constr; eauto.
    apply: ih_case; eauto.
    apply: ih_iota1; eauto.
    apply: ih_fix; eauto.
    apply: ih_iota2; eauto.
  Qed.
End pstep_ind_nested.

Definition sred σ τ :=
  forall x : var, (σ x) ~>* (τ x).

Fixpoint spine' (h : term) (ls : list term) : term :=
  match ls with
  | nil => h
  | m :: ls => App (spine' h ls) m
  end.

Lemma iget_All2 (P : term -> term -> Prop) xs ys x i :
  All2 P xs ys -> iget i xs x ->
  exists y, iget i ys y /\ P x y.
Proof.
  move=>a2. elim: a2 i x=>//={xs ys}.
  move=>i x ig. inv ig.
  move=>m m' ls ls' pm pls ih i x ig. inv ig.
  exists m'.
  split; eauto.
  constructor.
  have[y[ig pxy]]:=ih _ _ H3.
  exists y.
  split; eauto.
  constructor; eauto.
Qed.

Lemma iget_All2i (P : nat -> term -> term -> Prop) xs ys x i n :
  All2i P n xs ys -> iget i xs x ->
  exists y, iget i ys y /\ P (n + i) x y.
Proof.
  move=>a2. elim: a2 i x=>//={xs ys}.
  move=>i j x ig. inv ig.
  move=>i m m' ls ls' pm pls ih j x ig. inv ig.
  exists m'.
  split.
  constructor.
  rewrite addn0; eauto.
  have[y[ig pxy]]:=ih _ _ H3.
  exists y.
  split.
  constructor; eauto.
  rewrite<-addSnnS; eauto.
Qed.

Lemma One2_map R Q ls1 ls2 :
  (forall m n, R m n -> R (Q m) (Q n)) ->
  One2 R ls1 ls2 -> One2 R (map Q ls1) (map Q ls2).
Proof.
  move=>f One2. elim: One2 f.
  move=>m m' ls r f.
  constructor; eauto.
  move=>m ls ls' One2 ih f//=.
  constructor; eauto.
Qed.

Lemma rev_inj (ls1 ls2 : list term) : rev ls1 = rev ls2 -> ls1 = ls2.
Proof.
  move=>/(f_equal rev).
  by rewrite! revK.
Qed.

Lemma spine_append h xs ys :
  spine h (xs ++ ys) = spine (spine h xs) ys.
Proof. elim: xs ys h=>//=. Qed.

Lemma spine_rev h m ls :
  App (spine h (rev ls)) m = spine h (rev (m :: ls)).
Proof.
  elim: ls h m=>//.
  move=>t ls ih h m.
  rewrite<-cat1s.
  rewrite rev_cat.
  rewrite spine_append=>//=.
  rewrite<-cat1s.
  rewrite rev_cat.
  rewrite spine_append=>//=.
  by rewrite<-ih.
Qed.

Lemma spine_rev_spine' h ls : spine h (rev ls) = spine' h ls.
Proof.
  elim: ls h=>//=.
  move=>t ls ih h.
  rewrite<-ih.
  by rewrite spine_rev.
Qed.

Lemma spine_spine'_rev h ls : spine h ls = spine' h (rev ls).
Proof.
  have pf := spine_rev_spine' h (rev ls).
  by rewrite revK in pf.
Qed.

Lemma spine'_constr_inj i1 i2 h1 h2 ls1 ls2 :
  spine' (Constr i1 h1) ls1 = spine' (Constr i2 h2) ls2 ->
  i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  elim: ls1 ls2 i1 i2 h1 h2=>//=.
  move=>[|] i1 i2 h1 h2 e//=. by inv e.
  move=>t ls1 ih [|]//= t1 t2 i1 i2 h1 h2 [/ih[->[->->]]->]//.
Qed.

Lemma spine_constr_inj i1 i2 h1 h2 ls1 ls2 :
  spine (Constr i1 h1) ls1 = spine (Constr i2 h2) ls2 ->
  i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  rewrite!spine_spine'_rev=>/spine'_constr_inj[->[->/rev_inj->]]//.
Qed.

Lemma spine_subst σ h ls : (spine h ls).[σ] = spine h.[σ] ls..[σ].
Proof.
  elim: ls σ h=>//.
  move=>a ls ih σ h.
  replace ((a :: ls)..[σ]) with (a.[σ] :: ls..[σ]) by autosubst; simpl.
  replace (App h.[σ] a.[σ]) with (App h a).[σ] by autosubst.
  apply: ih.
Qed.

Lemma iget_iget ls i m1 m2 : iget i ls m1 -> iget i ls m2 -> m1 = m2.
Proof.
  move=>ig. elim: ig m2=>{ls}.
  move=>m ls m2 ig. by inv ig.
  move=>n m m' ls ig1 ih m2 ig2. inv ig2.
  by move: H3=>/ih.
Qed.

Lemma iget_subst σ i ls m : iget i ls m -> iget i ls..[σ] m.[σ].
Proof.
  move=>ig. elim: ig=>{m ls i}; asimpl.
  move=>m ls. by constructor.
  move=>n m m' ls ig ih. by constructor.
Qed.

Lemma step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof with eauto using step.
  move=>st. move: m n st σ. apply: step_ind_nested; asimpl...
  move=>A m n s t σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply step_beta. autosubst.
  move=>A Cs Cs' s h ih σ.
    constructor.
    elim: ih=>//=.
    move=>*. constructor. asimpl...
    move=>*. constructor. asimpl...
  move=>m Q Fs Fs' h ih σ.
    constructor.
    elim: ih=>//=.
    move=>*. constructor. asimpl...
    move=>*. constructor. asimpl...
  move=>i m ms Q Fs F ig σ.
    repeat (rewrite spine_subst; asimpl).
    constructor.
    exact: iget_subst.
  move=>A m σ.
    replace m.[Fix A m/].[σ] with m.[up σ].[Fix A.[σ] m.[up σ]/]
      by autosubst.
    constructor.
Qed.

Lemma red_app m m' n n' :
  m ~>* m' -> n ~>* n' -> App m n ~>* App m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App m' n)).
  apply: (star_hom (App^~ n)) r1=>x y. exact: step_appL.
  apply: star_hom r2. exact: step_appR.
Qed.

Lemma red_lam A A' m m' s t :
  A ~>* A' -> m ~>* m' -> Lam A m s t ~>* Lam A' m' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam A' m s t)).
  apply: (star_hom (((Lam^~ m)^~ s)^~ t)) r1=>x y. exact: step_lamL.
  apply: (star_hom (((Lam A')^~ s)^~ t)) r2=>x y. exact: step_lamR.
Qed.

Lemma red_pi A A' B B' s r t :
  A ~>* A' -> B ~>* B' -> Pi A B s r t ~>* Pi A' B' s r t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi A' B s r t)).
  apply: (star_hom ((((Pi^~ B)^~ s)^~ r)^~ t)) r1=>x y. exact: step_piL.
  apply: (star_hom ((((Pi A')^~ s)^~ r)^~ t)) r2=>x y. exact: step_piR.
Qed.

Lemma red_ind A1 A2 Cs1 Cs2 s :
  A1 ~>* A2 -> star (One2 step) Cs1 Cs2 -> Ind A1 Cs1 s ~>* Ind A2 Cs2 s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Ind A2 Cs1 s)).
  apply: (star_hom ((Ind^~ Cs1)^~ s)) r1=>x y. exact: step_indA.
  elim: r2=>//.
  move=>y z r2 r3 st.
  apply: star_trans.
  apply: r3.
  apply: star1.
  by constructor.
Qed.

Lemma red_constr i m1 m2 : m1 ~>* m2 -> Constr i m1 ~>* Constr i m2.
Proof.
  move=>r.
  apply: (star_hom (Constr i)) r=> x y. exact: step_constr.
Qed.

Lemma red_case m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 ~>* m2 -> Q1 ~>* Q2 -> star (One2 step) Fs1 Fs2 ->
  Case m1 Q1 Fs1 ~>* Case m2 Q2 Fs2.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (Case m2 Q1 Fs1)).
  apply: (star_hom ((Case^~ Q1)^~ Fs1)) r1=>x y. exact: step_caseM.
  apply: (star_trans (Case m2 Q2 Fs1)).
  apply: (star_hom ((Case m2)^~ Fs1)) r2=>x y. exact: step_caseQ.
  elim: r3=>//.
  move=>y z r3 r4 st.
  apply: star_trans.
  apply: r4.
  apply: star1.
  by constructor.
Qed.

Lemma red_fix A1 A2 m1 m2 : A1 ~>* A2 -> m1 ~>* m2 -> Fix A1 m1 ~>* Fix A2 m2.
Proof.
  move=>r1 r2.
  apply: (star_trans (Fix A2 m1)).
  apply: (star_hom (Fix^~ m1)) r1=>x y. exact: step_fixL.
  apply: (star_hom (Fix A2)) r2=>x y. exact: step_fixR.
Qed.

Lemma red_hd h1 h2 ls : h1 ~>* h2 -> star (One2 step) (h1 :: ls) (h2 :: ls).
Proof.
  move=>r. elim: r ls=>//.
  move=>y z r ih st ls.
  apply: star_trans.
  apply: ih.
  apply: star1.
  by constructor.
Qed.

Lemma red_tl h ls ls' :
  star (One2 step) ls ls' -> star (One2 step) (h :: ls) (h :: ls').
Proof.
  move=>r. elim: r h=>//.
  move=>y z r ih st h.
  apply: star_trans.
  apply: ih.
  apply: star1.
  by constructor.
Qed.

Lemma red_ls h1 h2 ls1 ls2 :
  h1 ~>* h2 -> star (One2 step) ls1 ls2 -> star (One2 step) (h1 :: ls1) (h2 :: ls2).
Proof.
  move=>hd tl.
  apply: star_trans.
  apply: red_hd.
  apply: hd.
  by apply: red_tl.
Qed.

Lemma red_nil_inv ls : star (One2 step) nil ls -> ls = nil.
Proof.
  elim=>//.
  move=>y z _ -> st. inv st.
Qed.

Lemma red_cons_inv m ls l :
  star (One2 step) (m :: ls) l ->
  exists m' ls',
    l = m' :: ls' /\ red m m' /\ star (One2 step) ls ls'.
Proof.
  elim=>//.
  exists m. exists ls=>//.
  move=>y z r[m0[ls0[->[r1 r2]]]] st. inv st.
  exists m'. exists ls0.
  repeat split; eauto.
  apply: starSE; eauto.
  exists m0. exists ls'.
  repeat split; eauto.
  apply: starSE; eauto.
Qed.

Lemma red_spine h1 h2 ls1 ls2 :
  h1 ~>* h2 -> star (One2 step) ls1 ls2 ->
  spine h1 ls1 ~>* spine h2 ls2.
Proof.
  elim: ls1 ls2 h1 h2.
  move=>ls2 h1 h2 rd/red_nil_inv->//.
  move=>a ls ih ls2 h1 h2 r1 r2=>//=.
  apply: (star_trans (spine (App h2 a) ls)).
  apply: ih=>//.
  by apply: red_app.
  move:r2=>/red_cons_inv[m[ls1[->[r2 r3]]]]//=.
  apply: ih=>//.
  by apply: red_app.
Qed.

Lemma red_subst m n σ : m ~>* n -> m.[σ] ~>* n.[σ].
Proof.
  move=>st.
  elim: st σ=>{n}; eauto.
  move=> n n' r ih st σ.
  move:(ih σ)=>{}ih.
  move:(step_subst σ st)=>r'.
  apply: star_trans.
  apply: ih.
  by apply: star1.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: red_subst. exact: A. Qed.

Hint Resolve
  red_app red_lam red_pi
  red_ind red_constr red_case red_fix
  red_ls red_subst sred_up : red_congr.

Lemma red_compat σ τ s : sred σ τ -> red s.[σ] s.[τ].
Proof with eauto 6 with red_congr.
  move: s σ τ.
  apply: term_ind_nested; asimpl...
  move=>A Cs s ih h σ τ sr.
  apply: red_ind...
  elim: h=>//=...
  move=>m Q Fs ih1 ih2 h σ τ sr.
  apply: red_case...
  elim: h=>//=...
Qed.

Definition sconv (σ τ : var -> term) :=
  forall x, σ x === τ x.

Lemma conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (App m' n)).
  apply: (conv_hom (App^~ n)) r1=>x y. exact: step_appL.
  apply: conv_hom r2. exact: step_appR.
Qed.

Lemma conv_lam A A' m m' s t :
  A === A' -> m === m' -> Lam A m s t === Lam A' m' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam A' m s t)).
  apply: (conv_hom (((Lam^~ m)^~ s)^~ t)) r1=>x y. exact: step_lamL.
  apply: (conv_hom (((Lam A')^~ s)^~ t)) r2=>x y. exact: step_lamR.
Qed.

Lemma conv_pi A A' B B' s r t :
  A === A' -> B === B' -> Pi A B s r t === Pi A' B' s r t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi A' B s r t)).
  apply: (conv_hom ((((Pi^~ B)^~ s)^~ r)^~ t)) r1=>x y. exact: step_piL.
  apply: (conv_hom ((((Pi A')^~ s)^~ r)^~ t)) r2=>x y. exact: step_piR.
Qed.

Lemma conv_ind A1 A2 Cs1 Cs2 s :
  A1 === A2 -> conv (One2 step) Cs1 Cs2 -> Ind A1 Cs1 s === Ind A2 Cs2 s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Ind A2 Cs1 s)).
  apply: (conv_hom ((Ind^~ Cs1)^~ s)) r1=>x y. exact: step_indA.
  elim: r2=>//.
  move=>y z r2 r3 st.
  apply: conv_trans.
  apply: r3.
  apply: conv1.
  by constructor.
  move=>y z r2 r3 st.
  apply: conv_trans.
  apply: r3.
  apply: conv1i.
  by constructor.
Qed.

Lemma conv_constr i m1 m2 : m1 === m2 -> Constr i m1 === Constr i m2.
Proof.
  move=>r.
  apply: (conv_hom (Constr i)) r=> x y. exact: step_constr.
Qed.

Lemma conv_case m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 === m2 -> Q1 === Q2 -> conv (One2 step) Fs1 Fs2 ->
  Case m1 Q1 Fs1 === Case m2 Q2 Fs2.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (Case m2 Q1 Fs1)).
  apply: (conv_hom ((Case^~ Q1)^~ Fs1)) r1=>x y. exact: step_caseM.
  apply: (conv_trans (Case m2 Q2 Fs1)).
  apply: (conv_hom ((Case m2)^~ Fs1)) r2=>x y. exact: step_caseQ.
  elim: r3=>//.
  move=>y z r3 r4 st.
  apply: conv_trans.
  apply: r4.
  apply: conv1.
  by constructor.
  move=>y z r3 r4 st.
  apply: conv_trans.
  apply: r4.
  apply: conv1i.
  by constructor.
Qed.

Lemma conv_fix A1 A2 m1 m2 : A1 === A2 -> m1 === m2 -> Fix A1 m1 === Fix A2 m2.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Fix A2 m1)).
  apply: (conv_hom (Fix^~ m1)) r1=>x y. exact: step_fixL.
  apply: (conv_hom (Fix A2)) r2=>x y. exact: step_fixR.
Qed.

Lemma conv_hd h1 h2 ls : h1 === h2 -> conv (One2 step) (h1 :: ls) (h2 :: ls).
Proof.
  move=>r. elim: r ls=>//.
  move=>y z r ih st ls.
  apply: conv_trans.
  apply: ih.
  apply: conv1.
  by constructor.
  move=>y z r ih st ls.
  apply: conv_trans.
  apply: ih.
  apply: conv1i.
  by constructor.
Qed.

Lemma conv_tl h ls ls' :
  conv (One2 step) ls ls' -> conv (One2 step) (h :: ls) (h :: ls').
Proof.
  move=>r. elim: r h=>//.
  move=>y z r ih st h.
  apply: conv_trans.
  apply: ih.
  apply: conv1.
  by constructor.
  move=>y z r ih st h.
  apply: conv_trans.
  apply: ih.
  apply: conv1i.
  by constructor.
Qed.

Lemma conv_ls h1 h2 ls1 ls2 :
  h1 === h2 -> conv (One2 step) ls1 ls2 -> conv (One2 step) (h1 :: ls1) (h2 :: ls2).
Proof.
  move=>hd tl.
  apply: conv_trans.
  apply: conv_hd.
  apply: hd.
  by apply: conv_tl.
Qed.

Lemma conv_subst σ s t :
  s === t -> s.[σ] === t.[σ].
Proof. 
  move=>c.
  apply: conv_hom c.
  exact: step_subst.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Hint Resolve
  conv_app conv_lam conv_pi
  conv_ind conv_constr conv_case conv_fix
  conv_ls sconv_up : conv_congr.

Lemma conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof with eauto with conv_congr.
  move: s σ τ.
  apply: term_ind_nested; asimpl...
  move=>A Cs s ih h σ τ sr.
  apply: conv_ind...
  elim: h=>//=...
  move=>m Q Fs ih1 ih2 h σ τ sr.
  apply: conv_case...
  elim: h=>//=...
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof with eauto using pstep, All2.
  move: s.
  apply: term_ind_nested...
  move=>A Cs s pA ih.
  constructor... elim: ih...
  move=>m Q Fs pm pQ ih.
  constructor... elim: ih...
Qed.
Hint Resolve pstep_refl.

Lemma All2_pstep_refl ls : All2 pstep ls ls.
Proof with eauto using pstep_refl, All2. elim: ls... Qed.
Hint Resolve All2_pstep_refl.

Lemma step_pstep m m' : m ~> m' -> pstep m m'.
Proof with eauto using pstep, All2.
  move: m m'.
  apply: step_ind_nested...
  move=>A Cs Cs' s h ih.
  constructor... elim: ih...
  move=>m Q Fs Fs' h ih.
  constructor... elim: ih...
Qed.

Lemma pstep_red m n : pstep m n -> m ~>* n.
Proof with eauto with red_congr.
  move: m n. apply: pstep_ind_nested=>//=...
  move=>A m m' n n' s t p1 r1 p2 r2.
    apply: starES.
    by constructor.
    apply: (star_trans m'.[n/]). exact: red_subst.
    by apply: red_compat=>-[|].
  move=>A A' Cs Cs' s pA rA pCs rCs.
    apply: red_ind...
    elim: rCs...
  move=>m m' Q Q' Fs Fs' pM rM pQ rQ pFs rFs.
    apply: red_case...
    elim: rFs...
  move=>i m ms ms' Q Fs Fs' F' ig pMs rMs pFs rFs.
    have ihMs : star (One2 step) ms ms'.
    { elim: rMs... }
    have ihFs : star (One2 step) Fs Fs'.
    { elim: rFs... }
    apply: star_trans.
    apply: red_case.
    apply: red_spine.
    apply: starR.
    apply: ihMs.
    apply: starR.
    apply: ihFs.
    apply: star1.
    by constructor.
  move=>A A' m m' pA rA pM rM.
    apply: star_trans.
    apply: red_fix...
    apply: star1.
    by constructor.
Qed.


Lemma pstep_subst m n σ : pstep m n -> pstep m.[σ] n.[σ].
Proof with eauto using pstep, All2.
  move=>p. move: m n p σ.
  apply: pstep_ind_nested...
  move=>A m m' n n' s t pm ihm pn ihn σ. asimpl.
    pose proof (ihm (up σ)) as ih1=>{ihm}.
    pose proof (ihn σ) as ih2=>{ihn}.
    pose proof (pstep_beta A.[σ] s t ih1 ih2) as h.
    by asimpl in h.
  move=>A A' Cs Cs' s pA ihA pCs ihCs σ. asimpl.
    constructor...
    elim: ihCs...
  move=>m m' Q Q' Fs Fs' pm ihm pQ iihQ pFs ihFs σ. asimpl.
    constructor...
    elim: ihFs...
  move=>i m ms ms' Q Fs Fs' F' ig pms ihMs pFs ihFs σ. asimpl.
    rewrite!spine_subst.
    apply: pstep_iota1.
    apply: iget_subst...
    elim: ihMs...
    elim: ihFs...
  move=>A A' m m' pA ihA pM ihM σ. asimpl.
    replace m'.[Fix A'.[σ] m'.[up σ] .: σ]
      with (m'.[up σ]).[Fix A'.[σ] m'.[up σ]/]
        by autosubst...
Qed.

Definition psstep (σ τ : var -> term) := 
  forall x, pstep (σ x) (τ x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl. elim... Qed.
Hint Resolve psstep_refl.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat m n σ τ :
  pstep m n -> psstep σ τ -> pstep m.[σ] n.[τ].
Proof with eauto 6 using pstep, All2, psstep_up.
  move=>p. move: m n p σ τ. apply: pstep_ind_nested...
  move=>A m m' n n' s t pm ihm pn ihn σ τ pss. asimpl.
    have pss' := psstep_up pss.
    have{}ihm := ihm _ _ pss'.
    have{}ihn := ihn _ _ pss.
    pose proof (pstep_beta A.[σ] s t ihm ihn) as h.
    by asimpl in h.
  move=>A A' Cs Cs' s pA ihA pCs ihCs σ τ pss. asimpl.
    constructor...
    elim: ihCs...
  move=>m m' Q Q' Fs Fs' pm ihm pQ ihQ pFs ihFs σ τ pss.
    constructor...
    elim: ihFs...
  move=>i m ms ms' Q Fs Fs' F' ig pms ihms pFs ihFs σ τ pss. asimpl.
    rewrite!spine_subst.
    apply: pstep_iota1.
    apply: iget_subst...
    elim: ihms...
    elim: ihFs...
  move=>A A' m m' pA ihA pm ihm σ τ pss. asimpl.
    replace m'.[Fix A'.[τ] m'.[up τ] .: τ]
      with (m'.[up τ]).[Fix A'.[τ] m'.[up τ]/]
      by autosubst...
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat.
  move...
Qed.

Lemma pstep_compat_beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat.
  move...
Qed.

Lemma pstep_iget1 ls ls' i m :
  All2 pstep ls ls' -> iget i ls m ->
  exists m', iget i ls' m' /\ pstep m m'.
Proof with eauto using iget.
  move=>p.
  elim: p m i=>{ls ls'}.
  move=>m i ig. inv ig.
  move=>m m' ls ls' p1 p2 ih m0 i ig. inv ig.
  exists m'...
  move: H3=>/ih[m1[ig p]].
  exists m1...
Qed.

Lemma pstep_iget2 ls ls' i m' :
  All2 pstep ls ls' -> iget i ls' m' ->
  exists m, iget i ls m /\ pstep m m'.
Proof with eauto using iget.
  move=>p.
  elim: p m' i=>{ls ls'}.
  move=>m' i ig. inv ig.
  move=>m m' ls ls' p1 p2 ih m0 i ig. inv ig.
  exists m...
  move: H3=>/ih[m1[ig p]].
  exists m1...
Qed.

Lemma pstep_spine h h' ls ls' :
  pstep h h' -> All2 pstep ls ls' -> pstep (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=>ls' h h' p1 p2. inv p2=>//.
  move=>a ls ih ls' h h' ph pls. inv pls=>//=.
  apply: ih=>//.
  constructor; eauto.
Qed.

Lemma spine'_lam_constr A m s t i h ls :
  ~Lam A m s t = spine' (Constr i h) ls.
Proof. elim: ls=>//. Qed.

Lemma pstep_spine'_inv i h ls m :
  pstep (spine' (Constr i h) ls) m ->
  exists h' ls',
    m = spine' (Constr i h') ls' /\
    pstep h h' /\
    All2 pstep ls ls'.
Proof with eauto using pstep, All2.
  elim: ls h m.
  move=>h m//=p. inv p.
  exists m'. exists nil...
  move=>a ls ih h m//=p. inv p.
  move:H1=>/ih[h'[ls'[->[p1 p2]]]].
  exists h'. exists (n' :: ls')...
  exfalso. apply: spine'_lam_constr; eauto.
Qed.

Lemma pstep_spine'_congr i h1 h2 ms1 ms2 :
  pstep (spine' (Constr i h1) ms1) (spine' (Constr i h2) ms2) ->
  All2 pstep ms1 ms2.
Proof with eauto using All2.
  elim: ms1 ms2 h2=>//=.
  destruct ms2=>//=...
  move=>h2 p. inv p.
  move=>a ls ih [|hd tl] h2 p//=.
  inv p. exfalso. apply: spine'_lam_constr; eauto.
  inv p.
  move: H2=>/ih...
  exfalso. apply: spine'_lam_constr; eauto.
Qed.

Lemma All2_pstep_append ls1 ls2 ls1' ls2' :
  All2 pstep ls1 ls2 -> All2 pstep ls1' ls2' ->
  All2 pstep (ls1 ++ ls1') (ls2 ++ ls2').
Proof with eauto using All2.
  move=>p. elim: p ls1' ls2'=>//={ls1 ls2}...
Qed.

Lemma All2_pstep_rev ls1 ls2 :
  All2 pstep ls1 ls2 -> All2 pstep (rev ls1) (rev ls2).
Proof with eauto using All2.
  elim=>//={ls1 ls2}...
  move=>m m' ls ls' p1 p2 p3.
  replace (m :: ls) with ([:: m] ++ ls) by eauto.
  replace (m' :: ls') with ([:: m'] ++ ls') by eauto.
  rewrite!rev_cat.
  apply: All2_pstep_append...
Qed.

Lemma pstep_spine_inv i h ls m :
  pstep (spine (Constr i h) ls) m ->
  ∃ h' ls',
    m = spine (Constr i h') ls' /\
    pstep h h' /\
    All2 pstep ls ls'.
Proof with eauto using pstep, All2.
  move=>p.
  have e:=revK ls.
  rewrite<-e in p.
  rewrite spine_spine'_rev in p.
  move: p=>/pstep_spine'_inv[h'[ls'[->[p1 p2]]]].
  exists h'. exists (rev ls').
  rewrite spine_spine'_rev.
  rewrite revK.
  rewrite revK in p2.
  repeat split...
  move/All2_pstep_rev in p2.
  by rewrite revK in p2.
Qed.

Lemma pstep_spine_congr i h1 h2 ms1 ms2 :
  pstep (spine (Constr i h1) ms1) (spine (Constr i h2) ms2) ->
  All2 pstep ms1 ms2.
Proof with eauto using pstep, All2.
  have<-:=revK ms1.
  have<-:=revK ms2.
  rewrite!spine_spine'_rev.
  move=>/pstep_spine'_congr.
  rewrite!revK=>/All2_pstep_rev.
  by rewrite!revK.
Qed.

Lemma All2_diamond ls ls1 ls2 :
  All2 pstep ls ls1 ->
  All2 pstep ls ls2 ->
  All2 (fun m m1 => forall m2, pstep m m2 -> exists2 m', pstep m1 m' & pstep m2 m') ls ls1 ->
  exists2 ls', All2 pstep ls1 ls' & All2 pstep ls2 ls'.
Proof with eauto using All2.
  move=>p1 p2 h. elim: h ls2 p1 p2=>{ls ls1}.
  move=>ls _ p. inv p. exists nil...
  move=>m m' ls ls' f p ih ls2 p1 p2.
  inv p1. inv p2.
  move: H1=>/f[mx p3 p4].
  have[lsx p5 p6]:=ih _ H4 H5.
  exists (mx :: lsx)...
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 -> exists2 m', pstep m1 m' & pstep m2 m'.
Proof with eauto 6 using 
  pstep, pstep_compat, pstep_compat_beta, psstep_compat, pstep_spine.
  move=>p. move: m m1 p m2. apply: pstep_ind_nested.
  move=>x m2 p. inv p. exists (Var x)...
  move=> s l m2 p. inv p. exists (s @ l)...
  move=> A A' n n' s t pA ihA pn ihn m2 p.
    inv p.
    have[A0 pA1 pA2]:=ihA _ H4.
    have[n0 pn1 pn2]:=ihn _ H5.
    exists (Lam A0 n0 s t)...
  move=> m m' n n' pm ihm pn ihn m2 p.
    inv p.
    have[m0 pm1 pm2]:=ihm _ H1.
    have[n0 pn1 pn2]:=ihn _ H3.
    exists (App m0 n0)...
    inv pm.
    have[n0 pn1 pn2]:=ihn _ H3.
    have pL : pstep (Lam A m0 s t) (Lam A' m'0 s t)...
    have[x px1 px2]:=ihm _ pL.
    inv px1. inv px2.
    exists (n'2.[n0/])...
  move=> A m m' n n' s t pm ihm pn ihn m2 p.
    inv p. inv H1.
    have[mx pm1 pm2]:=ihm _ H7.
    have[nx pn1 pn2]:=ihn _ H3.
    exists (mx.[nx/])...
    have[mx pm1 pm2]:=ihm _ H5.
    have[nx pn1 pn2]:=ihn _ H6.
    exists (mx.[nx/])...
  move=> A A' B B' s r t pA ihA pB ihB m2 p.
    inv p.
    have[Ax pA1 pA2]:=ihA _ H5.
    have[Bx pB1 pB2]:=ihB _ H6.
    exists (Pi Ax Bx s r t)...
  move=> A A' Cs Cs' s pA ihA pCs ihCs t p. inv p.
    move: H3=> /ihA [Ax pAx1 pAx2].
    move: (All2_diamond pCs H4 ihCs)=>[Csx pCsx1 pCsx2].
    exists (Ind Ax Csx s)...
  move=> i m m' pM ihM t p. inv p.
    move: H2=> /ihM [mx pMx1 pMx2].
    exists (Constr i mx)...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs t p. inv p.
    move: H2=> /ihM [mx pMx1 pMx2].
    move: H4=> /ihQ [Qx pQx1 pQx2].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx pFsx1 pFsx2].
    exists (Case mx Qx Fsx)...
    move: (pstep_spine_inv pM)=>[hx [msx[e[pM0 pMs]]]]; subst.
    have pf : pstep (spine (Constr i m0) ms) (spine (Constr i m0) ms').
      apply: pstep_spine...
    move: pf=> /ihM[mx pMx1 pMx2].
    move: (pstep_spine_inv pMx1)=>[hx'[msx'[e[pHx pMsx]]]]; subst.
    move: pMx2=>/pstep_spine_congr=> pMs'.
    move: (All2_diamond pFs H5 ihFs)=>[Fsx pFxs1 pFxs2].
    move: (pstep_iget1 pFxs2 H2)=> [Fx[ig pFx]].
    exists (spine Fx msx')...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs t p. inv p.
    move: H2=>/pstep_spine_inv[hx[mx[->[pM pMs']]]].
    move: (All2_diamond pMs pMs' ihMs)=>[mx' pMx1 pMx2].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx pFsx1 pFsx2].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    exists (spine Fx mx')...
    move: H=> /spine_constr_inj[e1[e2 e3]]; subst.
    move: (All2_diamond pMs H4 ihMs)=>[mx pMx1 pMx2].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx pFsx1 pFsx2].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    move: (pstep_iget2 pFsx2 igFx)=>[Fx'[igFx' pFx']].
    move: (iget_iget igFx' H2)=>e; subst.
    exists (spine Fx mx)...
  move=> A A' m m' pA ihA pM ihM t p. inv p.
    move: H1=> /ihA[Ax pAx1 pAx2].
    move: H3=> /ihM[mx pMx1 pMx2].
    exists (Fix Ax mx)...
    move: H1=> /ihA[Ax pAx1 pAx2].
    move: H3=> /ihM[mx pMx1 pMx2].
    exists (mx.[Fix Ax mx/])...
  move=> A A' m m' pA ihA pM ihM t p. inv p.
    move: H1=> /ihA[Ax pAx1 pAx2].
    move: H3=> /ihM[mx pMx1 pMx2].
    exists (mx.[Fix Ax mx/])...
    move: H1=> /ihA[Ax pAx1 pAx2].
    move: H3=> /ihM[mx pMx1 pMx2].
    exists (mx.[Fix Ax mx/])...
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> m ~>* m2 -> exists2 m', m1 ~>* m' & pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>m1 m2 r1 ih /step_pstep p1 m' p2.
  move:(ih _ p2)=>[m3 r2 p3].
  move:(pstep_diamond p1 p3)=>[m4 p4 p5].
  exists m4...
  apply: star_trans.
  apply: r2.
  by apply: pstep_red.
Qed.

Theorem confluence :
  confluent step.
Proof with eauto using step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r.
  elim: r z=>{y}.
  move=>z r. exists z...
  move=>y z r1 ih /step_pstep p z0 /ih[z1 r2 r3].
  move:(strip p r2)=>[z2 r4 p1].
  exists z2...
  apply: star_trans.
  apply r3.
  apply: pstep_red...
Qed.

Theorem church_rosser :
  CR step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma red_sort_inv s l A :
  s @ l ~>* A -> A = s @ l.
Proof.
  elim=>//y z r1 e r2; subst.
  inv r2.
Qed.

Lemma red_pi_inv A B s r t x :
  Pi A B s r t ~>* x -> 
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi A' B' s r t.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd [A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma red_var_inv x y : Var x ~>* y -> y = Var x.
Proof.
  elim=>//{} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma red_lam_inv A m x s t :
  Lam A m s t ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam A' m' s t.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma red_ind_inv A Cs s x :
  Ind A Cs s ~>* x ->
  exists A' Cs',
    A ~>* A' /\
    star (One2 step) Cs Cs' /\ x = Ind A' Cs' s.
Proof.
  elim.
  exists A. exists Cs=>//.
  move=>y z r1 [A'[Cs'[rA[rCs e]]]] r2. subst.
  inv r2.
  exists A'0. exists Cs'. eauto using star.
  exists A'. exists Cs'0. eauto using star.
Qed.

Lemma red_constr_inv i m x :
  Constr i m ~>* x ->
  exists m', m ~>* m' /\ x = Constr i m'.
Proof.
  elim.
  exists m=>//.
  move=>y z r1 [m'[r e]] r2. subst.
  inv r2.
  exists m'0. eauto using star.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  s1 @ l1 === s2 @ l2 -> s1 = s2 /\ l1 = l2.
Proof.
  move/church_rosser=>[x/red_sort_inv->/red_sort_inv[->->]]//.
Qed.

Lemma pi_inj A A' B B' s s' r r' t t' :
  Pi A B s r t === Pi A' B' s' r' t' ->
    A === A' /\ B === B' /\ s = s' /\ r = r' /\ t = t'.
Proof.
  move/church_rosser=>
    [x/red_pi_inv[A1[B1[rA1[rB1->]]]]
      /red_pi_inv[A2[B2[rA2[rB2[]]]]]] eA eB es er et; subst.
  repeat split.
  apply: conv_trans.
    apply: star_conv. by apply: rA1.
    apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
    apply: star_conv. by apply: rB1.
    apply: conv_sym. by apply: star_conv.
Qed.

Lemma All2_cat (P : term -> term -> Prop) xs1 xs2 ys1 ys2 :
  All2 P xs1 ys1 ->
  All2 P xs2 ys2 ->
  All2 P (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  move=>a2. elim: a2 xs2 ys2=>//=.
  move=> m m' ls ls' p a2 ih xs2 ys2 a2'.
  constructor; eauto.
Qed.

Lemma All2_rev (P : term -> term -> Prop) xs ys :
  All2 P xs ys -> All2 P (rev xs) (rev ys).
Proof.
  elim.
  rewrite /rev/catrev. constructor.
  move=> m m' ls ls' p a2 ih.
  replace (m :: ls) with ([:: m] ++ ls) by eauto.
  replace (m' :: ls') with ([:: m'] ++ ls') by eauto.
  rewrite! rev_cat.
  apply: All2_cat; eauto.
  rewrite /rev/catrev.
  repeat constructor; eauto.
Qed.

Lemma All2_red_refl ms : All2 red ms ms.
Proof with eauto using All2. elim: ms... Qed.

Lemma All2_conv_refl xs : All2 (conv step) xs xs.
Proof with eauto using All2. elim: xs... Qed.

Lemma One2_step_All2_red xs ys :
  One2 step xs ys -> All2 red xs ys.
Proof with eauto using star1, All2, All2_red_refl.
  elim=>{xs ys}.
  move=> m m' ls st...
  move=> m ls ls' o2 a2...
Qed.

Lemma One2_step_All2_conv xs ys :
  One2 step xs ys -> All2 (conv step) xs ys.
Proof with eauto using conv1, All2, All2_conv_refl.
  elim=>{xs ys}.
  move=> m m' ls st...
  move=> m ls ls' o2 a2...
Qed.

Lemma All2_red_trans xs ys zs :
  All2 red xs ys ->
  All2 red ys zs ->
  All2 red xs zs.
Proof.
  move=> a2. elim: a2 zs=>{xs ys}.
  move=> zs a2.
  inv a2.
  constructor.
  move=> m m' ls ls' rd a2 ih zs a2'.
  inv a2'.
  constructor; eauto.
  apply: star_trans; eauto.
Qed.

Lemma All2_conv_trans xs ys zs :
  All2 (conv step) xs ys ->
  All2 (conv step) ys zs ->
  All2 (conv step) xs zs.
Proof.
  move=> a2. elim: a2 zs=>{xs ys}.
  move=> zs a2.
  inv a2.
  constructor.
  move=> m m' ls ls' e a2 ih zs a2'.
  inv a2'.
  constructor; eauto.
  apply: conv_trans; eauto.
Qed.

Lemma All2_conv_sym xs ys :
  All2 (conv step) xs ys -> All2 (conv step) ys xs.
Proof.
  elim.
  constructor.
  move=> m m' ls ls' e a2 ih.
  constructor; eauto.
  apply: conv_sym; eauto.
Qed.

Lemma All2_red_conv xs ys :
  All2 red xs ys -> All2 (conv step) xs ys.
Proof with eauto using All2.
  elim...
  move=> m m' ls ls' rd a2 ih.
  constructor...
  apply: star_conv...
Qed.

Lemma star_One2_step_All2_conv xs ys :
  star (One2 step) xs ys -> All2 (conv step) xs ys.
Proof.
  elim.
  elim: xs; constructor; eauto.
  move=>y z st a2 o2.
  apply One2_step_All2_conv in o2.
  apply: All2_conv_trans; eauto.
Qed.

Lemma Ind_inj A A' Cs Cs' s s' :
  Ind A Cs s === Ind A' Cs' s' ->
  A === A' /\
  All2 (conv step) Cs Cs' /\
  s = s'.
Proof.
  move=>/church_rosser h. inv h.
  move: H=>/red_ind_inv[Ax[Csx[rA[rCs e]]]]; subst.
  move: H0=>/red_ind_inv[Ax'[Csx'[rA'[rCs' e']]]]; subst.
  inv e'.
  firstorder; eauto using join_conv.
  apply star_One2_step_All2_conv in rCs.
  apply star_One2_step_All2_conv in rCs'.
  apply: All2_conv_trans; eauto.
  apply: All2_conv_sym; eauto.
Qed.

Ltac red_inv m H :=
  match m with
  | Var    => apply red_var_inv in H
  | Sort   => apply red_sort_inv in H
  | Pi     => apply red_pi_inv in H
  | Lam    => apply red_lam_inv in H
  | Ind    => apply red_ind_inv in H
  | Constr => apply red_constr_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : red (?m _) _ |- _ ]         => red_inv m H
  | [ H : red (?m _ _) _ |- _ ]       => red_inv m H
  | [ H : red (?m _ _ _) _ |- _ ]     => red_inv m H
  | [ H : red (?m _ _ _ _) _ |- _ ]   => red_inv m H
  | [ H : red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : red ?m _ |- _ ]             => red_inv m H
  end;
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  end; eauto.
