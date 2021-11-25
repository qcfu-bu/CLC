From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS cilc_context cilc_ast.

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
| pstep_Var x :
  pstep (Var x) (Var x)
| pstep_Sort srt l :
  pstep (Sort srt l) (Sort srt l)
| pstep_Lam A A' n n' s : 
  pstep A A' ->
  pstep n n' -> 
  pstep (Lam A n s) (Lam A' n' s)
| pstep_App m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_Beta A m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam A m s) n) (m'.[n'/])
| pstep_Prod A A' s B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Prod A B s) 
        (Prod A' B' s)
| pstep_Lolli A A' s B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Lolli A B s) 
        (Lolli A' B' s)
| pstep_Ind A A' Cs Cs' s :
  pstep A A' ->
  All2 pstep Cs Cs' ->
  pstep (Ind A Cs s) (Ind A' Cs' s)
| pstep_Constr i m m' :
  pstep m m' ->
  pstep (Constr i m) (Constr i m')
| pstep_Case m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  All2 pstep Fs Fs' ->
  pstep (Case m Q Fs) (Case m' Q' Fs')
| pstep_CaseIota i m ms ms' Q Fs Fs' F' :
  iget i Fs' F' ->
  All2 pstep ms ms' ->
  All2 pstep Fs Fs' ->
  pstep 
    (Case (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_DCase m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  All2 pstep Fs Fs' ->
  pstep (DCase m Q Fs) (DCase m' Q' Fs')
| pstep_DCaseIota i m ms ms' Q Fs Fs' F' :
  iget i Fs' F' ->
  All2 pstep ms ms' ->
  All2 pstep Fs Fs' ->
  pstep 
    (DCase (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_Fix A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fix A m) (Fix A' m')
| pstep_Fiξota A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fix A m) (m'.[Fix A' m'/]).

Section pstep_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x) (Var x).
  Hypothesis ih_Sort : forall srt l, P (Sort srt l) (Sort srt l).
  Hypothesis ih_Lam : 
    forall A A' n n' s, pstep A A' -> P A A' -> pstep n n' -> P n n' -> 
      P (Lam A n s) (Lam A' n' s).
  Hypothesis ih_App :
    forall m m' n n', pstep m m' -> P m m' -> pstep n n' -> P n n' -> 
      P (App m n) (App m' n').
  Hypothesis ih_Beta :
    forall A m m' n n' s, pstep m m' -> P m m' -> pstep n n' -> P n n' ->
      P (App (Lam A m s) n) m'.[n'/].
  Hypothesis ih_Prod :
    forall A A' B B' s, pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Prod A B s) (Prod A' B' s).
  Hypothesis ih_Lolli :
    forall A A' B B' s, pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Lolli A B s) (Lolli A' B' s).
  Hypothesis ih_Ind :
    forall A A' Cs Cs' s, 
      pstep A A' -> P A A' -> 
      All2 pstep Cs Cs' -> All2 P Cs Cs' ->
      P (Ind A Cs s) (Ind A' Cs' s).
  Hypothesis ih_Constr :
    forall i m m', pstep m m' -> P m m' -> P (Constr i m) (Constr i m').
  Hypothesis ih_Case :
    forall m m' Q Q' Fs Fs', 
      pstep m m' -> P m m' -> 
      pstep Q Q' -> P Q Q' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (Case m Q Fs) (Case m' Q' Fs').
  Hypothesis ih_CaseIota :
    forall i m ms ms' Q Fs Fs' F',
      iget i Fs' F' ->
      All2 pstep ms ms' -> All2 P ms ms' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (Case (spine (Constr i m) ms) Q Fs) (spine F' ms').
  Hypothesis ih_DCase :
    forall m m' Q Q' Fs Fs', 
      pstep m m' -> P m m' -> 
      pstep Q Q' -> P Q Q' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (DCase m Q Fs) (DCase m' Q' Fs').
  Hypothesis ih_DCaseIota :
    forall i m ms ms' Q Fs Fs' F',
      iget i Fs' F' ->
      All2 pstep ms ms' -> All2 P ms ms' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (DCase (spine (Constr i m) ms) Q Fs) (spine F' ms').
  Hypothesis ih_Fix :
    forall A A' m m', pstep A A' -> P A A' -> pstep m m' -> P m m' -> 
      P (Fix A m) (Fix A' m').
  Hypothesis ih_Fiξota :
    forall A A' m m', pstep A A' -> P A A' -> pstep m m' -> P m m' -> 
      P (Fix A m) (m'.[Fix A' m'/]).
  
  Fixpoint pstep_ind_nested m m' (st : pstep m m') : P m m'.
  Proof.
    pose ih_nested := (
      fix fold ls1 ls2 (p : All2 pstep ls1 ls2) : All2 P ls1 ls2 :=
        match p with
        | All2_nil => All2_nil _
        | All2_cons _ _ _ _ hd tl =>
          All2_cons (pstep_ind_nested _ _ hd) (fold _ _ tl)
        end).
    case st; intros.
    apply ih_Var.
    apply ih_Sort.
    apply ih_Lam; eauto.
    apply ih_App; eauto.
    apply ih_Beta; eauto.
    apply ih_Prod; eauto.
    apply ih_Lolli; eauto.
    apply ih_Ind; eauto.
    apply ih_Constr; eauto.
    apply ih_Case; eauto.
    eapply ih_CaseIota; eauto.
    apply ih_DCase; eauto.
    eapply ih_DCaseIota; eauto.
    apply ih_Fix; eauto.
    apply ih_Fiξota; eauto.
  Qed.
End pstep_ind_nested.

Definition sred σ tau := 
  forall x : var, red (σ x) (tau x).

Fixpoint spine' (h : term) (ls : list term) : term :=
  match ls with
  | nil => h
  | m :: ls => App (spine' h ls) m
  end.

Lemma iget_All2 (P : term -> term -> Prop) xs ys x i :
  All2 (fun x y => P x y) xs ys ->
  iget i xs x ->
  exists y,
    iget i ys y /\ P x y.
Proof.
  move=>a2. elim: a2 i x=>//={xs ys}; intros.
  { inv H. }
  { inv H2.
    { exists m'. 
      split.
      constructor.
      apply: H. }
    { move: (H1 _ _ H7)=>[y[ig pxy]].
      exists y.
      split.
      constructor; eauto.
      apply: pxy. } }
Qed.

Lemma iget_All2i (P : nat -> term -> term -> Prop) xs ys x i n :
  All2i (fun i x y => P i x y) n xs ys ->
  iget i xs x ->
  exists y,
    iget i ys y /\ P (n + i) x y.
Proof.
  move=>a2. elim: a2 i x=>//={xs ys}; intros.
  { inv H. }
  { inv H2.
    { exists m'.
      split.
      constructor.
      rewrite addn0; eauto. }
    { move: (H1 _ _ H7)=>[y[ig pxy]].
      exists y.
      split.
      constructor; eauto.
      rewrite <-addSnnS; eauto. } }
Qed.

Lemma One2_map R Q ls1 ls2 :
  (forall m n, R m n -> R (Q m) (Q n)) -> 
    One2 R ls1 ls2 -> One2 R (map Q ls1) (map Q ls2).
Proof.
  move=> f One2.
  elim: One2 f.
  move=> m m' ls r f.
    constructor.
    exact: f.
  move=> m ls ls' One2 ih f //=.
    constructor.
    exact: ih.
Qed.

Lemma rev_inj (ls1 ls2 : list term) : rev ls1 = rev ls2 -> ls1 = ls2.
Proof.
  move=> e.
  move:e=> /(f_equal rev).
  by rewrite! revK.
Qed.

Lemma spine_append h xs ys :
  spine h (xs ++ ys) = spine (spine h xs) ys.
Proof. elim: xs ys h=> //=. Qed.

Lemma spine_rev h m ls :
  App (spine h (rev ls)) m = spine h (rev (m :: ls)).
Proof.
  elim: ls h m=> //=.
  move=> t ls ih h m.
  rewrite <-cat1s.
  rewrite rev_cat.
  rewrite spine_append=> //=.
  rewrite <-cat1s.
  rewrite rev_cat.
  rewrite spine_append=> //=.
  by rewrite <- ih.
Qed.

Lemma spine_rev_spine' h ls :
  spine h (rev ls) = spine' h ls.
Proof.
  elim: ls h=> //=.
  move=> t t0 ih h.
  rewrite <- ih.
  by rewrite spine_rev.
Qed.

Lemma spine_spine'_rev h ls :
  spine h ls = spine' h (rev ls).
Proof.
  have pf := spine_rev_spine' h (rev ls).
  by rewrite revK in pf.
Qed.

Lemma spine'_Constr_inj i1 i2 h1 h2 ls1 ls2 :
  spine' (Constr i1 h1) ls1 = spine' (Constr i2 h2) ls2 ->
    i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  elim: ls1 ls2 i1 i2 h1 h2=>//=.
  move=> ls2 i1 i2 h1 h2.
    destruct ls2=> //= e. by inv e.
  move=> t ls1 ih ls2 t1 t2 h1 h2.
    destruct ls2=> //= e.
    inv e.
    by move: H0=> /ih [->[->->]].
Qed.

Lemma spine_Constr_inj i1 i2 h1 h2 ls1 ls2 :
  spine (Constr i1 h1) ls1 = spine (Constr i2 h2) ls2 ->
    i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  rewrite! spine_spine'_rev=> /spine'_Constr_inj[->[->e]].
  by move: e=> /rev_inj->.
Qed.

Lemma spine_subst σ h ls :
  (spine h ls).[σ] = spine (h.[σ]) ls..[σ].
Proof.
  move: σ h. elim: ls => //.
  move=> a l ih σ h.
    replace ((a :: l)..[σ]) 
      with (a.[σ] :: l..[σ])
      by autosubst; simpl.
    replace (App h.[σ] a.[σ]) with (App h a).[σ]
      by autosubst.
    apply ih.
Qed.

Lemma iget_iget ls i m1 m2 :
  iget i ls m1 -> iget i ls m2 -> m1 = m2.
Proof.
  move=> ig. elim: ig m2.
  move=> m ls0 m2 ig. by inv ig.
  move=> n m m' ls0 ig1 ih m2 ig2. inv ig2.
    by move: H3=> /ih.
Qed.

Lemma iget_subst σ i ls m :
  iget i ls m -> iget i ls..[σ] m.[σ].
Proof.
  move=> ig. elim: ig; asimpl.
  move=> m0 ls0; by constructor.
  move=> n m0 m' ls0 ig ih; by constructor.
Qed.

Lemma step_subst σ m n (st : step m n) : 
  step m.[σ] n.[σ].
Proof with eauto using step.
  move: m n st σ.
  apply: step_ind_nested; asimpl... 
  move=> A m n s σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/])
    by autosubst.
    exact: step_Beta.
  move=> A s Cs Cs' h ih σ; asimpl. 
    constructor.
    elim: ih=> //=.
    intros; constructor; asimpl...
    intros; constructor; asimpl...
  move=> m Q Fs Fs' h ih σ; asimpl.
    constructor.
    elim: ih=> //=.
    intros; constructor; asimpl...
    intros; constructor; asimpl...
  move=> i m ms Q Fs F ig σ.
    repeat (rewrite spine_subst; asimpl).
    constructor.
    exact: iget_subst.
  move=> m Q Fs Fs' h ih σ; asimpl.
    constructor.
    elim: ih=> //=.
    intros; constructor; asimpl...
    intros; constructor; asimpl...
  move=> i m ms Q Fs F ig σ; asimpl.
    repeat (rewrite spine_subst; asimpl).
    constructor.
    exact: iget_subst.
  move=> A m σ.
    replace m.[Fix A m/].[σ] with m.[up σ].[Fix A.[σ] m.[up σ]/]
      by autosubst.
    constructor.
Qed.

Lemma red_App m1 m2 n1 n2 :
  red m1 m2 -> red n1 n2 -> red (App m1 n1) (App m2 n2).
Proof.
  move=> A B. apply: (star_trans (App m2 n1)).
  apply: (star_hom (App^~ n1)) A=> x y. exact: step_AppL.
  apply: star_hom B=> x y. exact: step_AppR.
Qed.

Lemma red_Lam A1 A2 n1 n2 s : 
  red A1 A2 -> red n1 n2 -> red (Lam A1 n1 s) (Lam A2 n2 s).
Proof. 
  move=> A B. apply: (star_trans (Lam A2 n1 s)).
  apply: (star_hom ((Lam^~ n1)^~ s)) A=> x y. exact: step_LamL.
  apply: (star_hom ((Lam A2)^~ s)) B=> x y. exact: step_LamR. 
Qed.

Lemma red_Prod A1 A2 B1 B2 s :
  red A1 A2 -> red B1 B2 -> red (Prod A1 B1 s) (Prod A2 B2 s).
Proof.
  move=> A B. apply: (star_trans (Prod A2 B1 s)).
  apply: (star_hom ((Prod^~ B1)^~ s)) A=> x y. exact: step_ProdL.
  apply: (star_hom ((Prod A2)^~ s)) B => x y. exact: step_ProdR.
Qed.

Lemma red_Lolli A1 A2 B1 B2 s :
  red A1 A2 -> red B1 B2 -> red (Lolli A1 B1 s) (Lolli A2 B2 s).
Proof.
  move=> A B. apply: (star_trans (Lolli A2 B1 s)).
  apply: (star_hom ((Lolli^~ B1)^~ s)) A=> x y. exact: step_LolliL.
  apply: (star_hom ((Lolli A2)^~ s)) B=> x y. exact: step_LolliR.
Qed.

Lemma red_Ind A1 A2 Cs1 Cs2 s :
  red A1 A2 -> star (One2 step) Cs1 Cs2 -> 
    red (Ind A1 Cs1 s) (Ind A2 Cs2 s).
Proof.
  move=> A B. 
  apply: (star_trans (Ind A2 Cs1 s)).
  apply: (star_hom ((Ind^~ Cs1)^~ s)) A=> x y. exact: step_IndA.
  elim: B=> //.
    move=> y z rd' rd st.
    apply: star_trans.
      by apply: rd.
      by apply: star1; eauto using step.
Qed.

Lemma red_Constr i m1 m2 :
  red m1 m2 -> red (Constr i m1) (Constr i m2).
Proof.
  move=> A.
  apply: (star_hom (Constr i)) A => x y. exact: step_Constr.
Qed.

Lemma red_Case m1 m2 Q1 Q2 Fs1 Fs2 :
  red m1 m2 -> red Q1 Q2 -> star (One2 step) Fs1 Fs2 -> 
    red (Case m1 Q1 Fs1) (Case m2 Q2 Fs2).
Proof.
  move=> A B C. 
  apply: (star_trans (Case m2 Q1 Fs1)).
  apply: (star_hom ((Case^~ Q1)^~ Fs1)) A=> x y. exact: step_CaseM.
  apply: (star_trans (Case m2 Q2 Fs1)).
  apply: (star_hom ((Case m2)^~ Fs1)) B=> x y. exact: step_CaseQ.
  elim: C=> //.
    move=> y z rd' rd st.
    apply: star_trans.
      by apply: rd.
      by apply: star1; eauto using step.
Qed.

Lemma red_DCase m1 m2 Q1 Q2 Fs1 Fs2 :
  red m1 m2 -> red Q1 Q2 -> star (One2 step) Fs1 Fs2 -> 
    red (DCase m1 Q1 Fs1) (DCase m2 Q2 Fs2).
Proof.
  move=> A B C. 
  apply: (star_trans (DCase m2 Q1 Fs1)).
  apply: (star_hom ((DCase^~ Q1)^~ Fs1)) A=> x y. exact: step_DCaseM.
  apply: (star_trans (DCase m2 Q2 Fs1)).
  apply: (star_hom ((DCase m2)^~ Fs1)) B=> x y. exact: step_DCaseQ.
  elim: C=> //.
    move=> y z rd' rd st.
    apply: star_trans.
      by apply: rd.
      by apply: star1; eauto using step.
Qed.

Lemma red_Fix A1 A2 m1 m2 :
  red A1 A2 -> red m1 m2 -> red (Fix A1 m1) (Fix A2 m2).
Proof.
  move=> A B. apply: (star_trans (Fix A2 m1)).
  apply: (star_hom (Fix^~ m1)) A=> x y. exact: step_FixL.
  apply: (star_hom (Fix A2)) B=> x y. exact: step_FixR.
Qed.

Lemma red_hd h1 h2 ls :
  red h1 h2 -> star (One2 step) (h1 :: ls) (h2 :: ls).
Proof.
  move=> rd. elim: rd ls=> //.
  move=> y z rd ih st ls.
  apply: star_trans.
    by apply: ih.
    by apply: star1; constructor.
Qed.

Lemma red_tl h ls ls' :
  star (One2 step) ls ls' -> star (One2 step) (h :: ls) (h :: ls').
Proof.
  move=> rd. elim: rd h=> //.
  move=> y z rd ih st h.
  apply: star_trans.
    by apply: ih.
    by apply: star1; constructor.
Qed.

Lemma red_ls h h' ls ls' :
  red h h' ->
  star (One2 step) ls ls' -> 
  star (One2 step) (h :: ls) (h' :: ls').
Proof.
  move=> hd tl.
  apply: star_trans.
    apply: red_hd.
    apply: hd.
    exact: red_tl.
Qed.

Lemma red_nil_inv ls : star (One2 step) nil ls -> ls = nil.
Proof. 
  elim=> //.
  move=> y z _ -> st. by inv st.
Qed.

Lemma red_cons_inv m ls l : 
  star (One2 step) (m :: ls) l -> 
  exists m' ls', 
    l = m' :: ls' /\ red m m' /\ star (One2 step) ls ls'.
Proof.
  elim=> //.
  by exists m; exists ls=> //.
  move=> y z rd [m0 [ls0 [-> [rd1 rd2]]]] st. inv st.
    exists m'; exists ls0; split=> //.
      split. apply: starSE. exact: rd1. exact: H2. exact: rd2.
    exists m0; exists ls'; split=> //.
      split. exact: rd1. apply: starSE. exact: rd2. exact: H2.
Qed.

Lemma red_spine h h' ls ls' :
  red h h' -> star (One2 step) ls ls' -> 
    red (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=> ls' h h' rd /red_nil_inv -> //.
  move=> t t0 ih ls' h h' rd rd'=> //=.
  apply: (star_trans (spine (App h' t) t0)).  
    apply: ih=> //.
    exact: red_App.
  move: rd'=> /red_cons_inv [m [ls [-> [rd1 rd2]]]] //=.
    apply: ih.
    exact: red_App.
    exact: rd2.
Qed.

Lemma red_subst σ m n :
  red m n -> red m.[σ] n.[σ].
Proof.
  move=> rd. elim: rd σ=> /={n}.
  move=> σ //.
  move=> y z rd ih st σ.
    have rd1 := ih σ.
    apply: star_trans.
    apply: rd1.
    move: st=> /(step_subst σ) rd2.
    by apply: star1.
Qed.

Lemma sred_up σ tau : 
  sred σ tau -> sred (up σ) (up tau).
Proof. 
  move=> A [|n] //=; asimpl. 
  apply: red_subst. 
  exact: A. 
Qed.

Hint Resolve 
  red_App red_Lam red_Prod red_Lolli 
  red_Ind red_Constr red_Case red_DCase red_Fix
  red_ls red_subst sred_up 
: red_congr.

Lemma red_compat σ tau s : 
  sred σ tau -> red s.[σ] s.[tau].
Proof.
  move: s σ tau.
  apply: term_ind_nested; asimpl; eauto 6 with red_congr.
  move=> A s Cs ih h σ tau sr.
    apply: red_Ind; eauto.
    elim: h=> //=; eauto 6 with red_congr.
  move=> m Q Fs ih1 ih2 ih3 σ tau sr.
    apply: red_Case; eauto.
    elim: ih3=> //=; eauto 6 with red_congr.
  move=> m Q Fs ih1 ih2 ih3 σ tau sr.
    apply: red_DCase; eauto.
    elim: ih3=> //=; eauto 6 with red_congr.
Qed.

Definition sconv (σ tau : var -> term) := 
  forall x, σ x === tau x.

Lemma conv_Lam A1 A2 m1 m2 s : 
  A1 === A2 -> m1 === m2 -> Lam A1 m1 s === Lam A2 m2 s.
Proof. 
  move=> A B.
  apply: (conv_trans (Lam A2 m1 s)).
  apply: (conv_hom ((Lam^~ m1)^~ s)) A=> x y. exact: step_LamL.
  apply: (conv_hom ((Lam A2)^~ s)) B=> x y. exact: step_LamR.
Qed.

Lemma conv_Prod A1 A2 s B1 B2 :
  A1 === A2 -> B1 === B2 -> Prod A1 B1 s === Prod A2 B2 s.
Proof.
  move=> A B.
  apply: (conv_trans (Prod A2 B1 s)).
  apply: (conv_hom ((Prod^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Prod A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_Lolli A1 A2 s B1 B2 :
  A1 === A2 -> B1 === B2 -> Lolli A1 B1 s === Lolli A2 B2 s.
Proof.
  move=> A B.
  apply: (conv_trans (Lolli A2 B1 s)).
  apply: (conv_hom ((Lolli^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Lolli A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_App m1 m2 n1 n2 :
  m1 === m2 -> n1 === n2 -> App m1 n1 === App m2 n2.
Proof.
  move=> A B.
  apply: (conv_trans (App m2 n1)).
  apply: (conv_hom (App^~ n1)) A=> x y ps.
    by constructor.
  apply: conv_hom B=> x y ps.
    by constructor.
Qed.

Lemma conv_Ind A1 A2 Cs1 Cs2 s :
  A1 === A2 -> conv (One2 step) Cs1 Cs2 -> Ind A1 Cs1 s === Ind A2 Cs2 s.
Proof.
  move=> A B. 
  apply: (conv_trans (Ind A2 Cs1 s)).
  apply: (conv_hom ((Ind^~ Cs1)^~ s)) A=> x y. exact: step_IndA.
  elim: B=> //.
    move=> y z cv' cv st.
    apply: (conv_trans (Ind A2 y s)).
      by apply: cv.
      by apply: conv1; eauto using step.
    move=> y z cv' cv st.
    apply: (conv_trans (Ind A2 y s)).
      by apply: cv.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_Constr i m1 m2 :
  m1 === m2 -> Constr i m1 === Constr i m2.
Proof.
  move=> A.
  apply: (conv_hom (Constr i)) A => x y. exact: step_Constr.
Qed.

Lemma conv_Case m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 === m2 -> 
  Q1 === Q2 -> 
  conv (One2 step) Fs1 Fs2 -> 
  Case m1 Q1 Fs1 === Case m2 Q2 Fs2.
Proof.
  move=> A B C. 
  apply: (conv_trans (Case m2 Q1 Fs1)).
  apply: (conv_hom ((Case^~ Q1)^~ Fs1)) A=> x y. exact: step_CaseM.
  apply: (conv_trans (Case m2 Q2 Fs1)).
  apply: (conv_hom ((Case m2)^~ Fs1)) B=> x y. exact: step_CaseQ.
  elim: C=> //.
    move=> y z cv' cv st.
    apply: conv_trans.
      by apply: cv.
      by apply: conv1; eauto using step.
    move=> y z cv' cv st.
    apply: conv_trans.
      by apply: cv.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_DCase m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 === m2 -> 
  Q1 === Q2 -> 
  conv (One2 step) Fs1 Fs2 -> 
  DCase m1 Q1 Fs1 === DCase m2 Q2 Fs2.
Proof.
  move=> A B C. 
  apply: (conv_trans (DCase m2 Q1 Fs1)).
  apply: (conv_hom ((DCase^~ Q1)^~ Fs1)) A=> x y. exact: step_DCaseM.
  apply: (conv_trans (DCase m2 Q2 Fs1)).
  apply: (conv_hom ((DCase m2)^~ Fs1)) B=> x y. exact: step_DCaseQ.
  elim: C=> //.
    move=> y z rd' rd st.
    apply: conv_trans.
      by apply: rd.
      by apply: conv1; eauto using step.
    move=> y z rd' rd st.
    apply: conv_trans.
      by apply: rd.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_Fix A1 A2 m1 m2 :
  A1 === A2 -> m1 === m2 -> Fix A1 m1 === Fix A2 m2.
Proof.
  move=> A B.
  apply: (conv_trans (Fix A2 m1)).
  apply: (conv_hom (Fix^~ m1)) A=> x y. exact: step_FixL.
  apply: (conv_hom (Fix A2)) B=> x y. exact: step_FixR.
Qed.

Lemma conv_hd h1 h2 ls :
  h1 === h2 -> conv (One2 step) (h1 :: ls) (h2 :: ls).
Proof.
  move=> cv. elim: cv ls=> //.
  move=> y z cv ih st ls.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1; constructor.
  move=> y z rd ih st ls.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1i; constructor.
Qed.

Lemma conv_tl h ls ls' :
  conv (One2 step) ls ls' -> conv (One2 step) (h :: ls) (h :: ls').
Proof.
  move=> cv. elim: cv h=> //.
  move=> y z cv ih st h.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1; constructor.
  move=> y z cv ih st h.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1i; constructor.
Qed.

Lemma conv_ls h h' ls ls' :
  h === h' ->
  conv (One2 step) ls ls' -> 
  conv (One2 step) (h :: ls) (h' :: ls').
Proof.
  move=> hd tl.
  apply: conv_trans.
    apply: conv_hd.
    apply: hd.
    exact: conv_tl.
Qed.

Lemma conv_subst σ m n :
  m === n -> m.[σ] === n.[σ].
Proof.
  move=> cv. elim: cv σ=> /={n}.
  move=> σ //.
  move=> y z rd ih st σ.
    have cv1 := ih σ.
    apply: conv_trans.
    apply: cv1.
    move: st=> /(step_subst σ) rd2.
    by apply: conv1.
  move=> y z rd ih st σ.
    have cv1 := ih σ.
    apply: conv_trans.
    apply: cv1.
    move: st=> /(step_subst σ) rd2.
    by apply: conv1i.
Qed.

Lemma sconv_up σ tau : 
  sconv σ tau -> sconv (up σ) (up tau).
Proof. 
  move=> A [|n] //=; asimpl. 
  apply: conv_subst. 
  exact: A. 
Qed.

Hint Resolve 
  conv_App conv_Lam conv_Prod conv_Lolli 
  conv_Ind conv_Constr conv_Case conv_DCase conv_Fix
  conv_ls conv_subst sconv_up 
: conv_congr.

Lemma conv_compat σ tau s : 
  sconv σ tau -> s.[σ] === s.[tau].
Proof.
  move: s σ tau.
  apply: term_ind_nested; asimpl; eauto 6 with conv_congr. 
  move=> A s Cs ih h σ tau sr.
    apply: conv_Ind; eauto.
    elim: h=> //=; eauto 6 with conv_congr.
  move=> m Q Fs ih1 ih2 ih3 σ tau sr.
    apply: conv_Case; eauto.
    elim: ih3=> //=; eauto 6 with conv_congr.
  move=> m Q Fs ih1 ih2 ih3 σ tau sr.
    apply: conv_DCase; eauto.
    elim: ih3=> //=; eauto 6 with conv_congr.
Qed.

Lemma conv_Beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof.
  move: s.
  apply: term_ind_nested; eauto using pstep. 
  move=> A Cs s pA ih.
    constructor; eauto.
    elim: ih; eauto using pstep, All2.
  move=> m Q Fs pm pQ ih.
    constructor; eauto.
    elim: ih; eauto using pstep, All2.
  move=> m Q Fs pm pQ ih.
    constructor; eauto.
    elim: ih; eauto using pstep, All2.
Qed.

Lemma All2_pstep_refl ls : All2 pstep ls ls.
Proof with eauto using pstep_refl, All2. elim: ls... Qed.

Lemma step_pstep m m' : step m m' -> pstep m m'.
Proof with eauto using pstep, pstep_refl, All2, All2_pstep_refl.
  move: m m'.
  apply: step_ind_nested...
  intros; constructor...
    elim: H0...
  intros; constructor...
    elim: H0...
  intros; constructor...
    elim: H0...
Qed.

Lemma pstep_red m m' : pstep m m' -> red m m'.
Proof.
  move: m m'.
  apply: pstep_ind_nested=> //=; eauto with red_congr.
  move=> A m m' n n' s p1 r1 p2 r2.
    apply: starES.
    by econstructor.
    apply: (star_trans (m'.[n.:Var])). exact: red_subst.
    by apply: red_compat => -[|].
  move=> A A' s Cs Cs' pA rA pCs rCs.
    apply: red_Ind; eauto.
    elim: rCs; eauto with red_congr.
  move=> m m' Q Q' Fs Fs' pM rM pQ rQ pFs rFs.
    apply: red_Case; eauto.
    elim: rFs; eauto with red_congr.
  move=> i m ms ms' Q Fs Fs' F' ig pMs rMs pFs rFs.
    have ihMs : star (One2 step) ms ms'.
      elim: rMs; eauto with red_congr.
    have ihFs : star (One2 step) Fs Fs'.
      elim: rFs; eauto with red_congr.
    apply: star_trans.
    apply: red_Case.
    apply: red_spine.
    exact: starR.
    exact: ihMs.
    exact: starR.
    exact: ihFs.
    apply: star1.
    by constructor.
  move=> m m' Q Q' Fs Fs' pM rM pQ rQ pFs rFs.
    apply: red_DCase; eauto.
    elim: rFs; eauto with red_congr.
  move=> i m ms ms' Q Fs Fs' F' ig pMs rMs pFs rFs.
    have ihMs : star (One2 step) ms ms'.
      elim: rMs; eauto with red_congr.
    have ihFs : star (One2 step) Fs Fs'.
      elim: rFs; eauto with red_congr.
    apply: star_trans.
    apply: red_DCase.
    apply: red_spine.
    exact: starR.
    exact: ihMs.
    exact: starR.
    exact: ihFs.
    apply: star1.
    by constructor.
  move=> A A' m m' pA rA pM rM.
    apply: star_trans.
    apply: red_Fix.
    exact: rA.
    exact: rM.
    apply: star1.
    by constructor.
Qed.

Lemma pstep_subst σ m m' :
  pstep m m' -> pstep m.[σ] m'.[σ].
Proof with eauto using pstep, pstep_refl, All2, All2_pstep_refl.
  move=> p. move: m m' p σ.
  apply: pstep_ind_nested...
  move=> A m m' n n' s p1 ih1 p2 ih2 σ; asimpl.
    pose proof (ih1 (up σ))=> {ih1}.
    pose proof (ih2 σ)=> {ih2}.
    pose proof (pstep_Beta A.[σ] s H H0).
    by asimpl in H1.
  move=> A A' s Cs Cs' pA ihA pCs ihCs σ; asimpl.
    constructor; eauto.
    elim: ihCs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs σ; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs σ; asimpl.
    rewrite! spine_subst.
    apply: pstep_CaseIota; eauto.
    apply: iget_subst. exact ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs σ; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs σ; asimpl.
    rewrite! spine_subst.
    apply: pstep_DCaseIota; eauto.
    apply: iget_subst. exact ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> A A' m m' pA ihA pM ihM σ; asimpl.
    replace m'.[Fix A'.[σ] m'.[up σ] .: σ]
      with (m'.[up σ]).[Fix A'.[σ] m'.[up σ]/]
      by autosubst.
    exact: pstep_Fiξota.
Qed.

Definition psstep (σ tau : var -> term) := 
  forall x, pstep (σ x) (tau x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl.
  unfold psstep.
  induction x...
Qed.

Lemma psstep_up σ tau :
  psstep σ tau -> psstep (up σ) (up tau).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat σ tau m m' :
  pstep m m' -> psstep σ tau -> pstep m.[σ] m'.[tau].
Proof with eauto 6 using pstep, All2, psstep_up.
  move=> p. move: m m' p σ tau.
  apply: pstep_ind_nested... 
  move=> A m m' n n' s pM ihM pN ihN σ tau pss; asimpl.
    have pss' := psstep_up pss.
    have hM := ihM _ _ pss'.
    have hN := ihN _ _ pss.
    pose proof (pstep_Beta (A.[σ]) s hM hN).
    by asimpl in H.
  move=> A A' Cs Cs' s pA ihA pCs ihCs σ tau pss; asimpl.
    constructor; eauto.
    elim: ihCs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs σ tau pss; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs σ tau pss; asimpl.
    rewrite! spine_subst.
    apply: pstep_CaseIota.
    apply: iget_subst. exact: ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs σ tau pss; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs σ tau pss; asimpl.
    rewrite! spine_subst.
    apply: pstep_DCaseIota.
    apply: iget_subst. exact: ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> A A' m m' pA ihA pM ihM σ tau ps; asimpl.
    replace m'.[Fix A'.[tau] m'.[up tau] .: tau]
      with (m'.[up tau]).[Fix A'.[tau] m'.[up tau]/]
      by autosubst.
    constructor.
    exact: ihA.
    apply: ihM.
    exact: psstep_up.
Qed.

Lemma psstep_compat σ tau m1 m2 :
  psstep σ tau -> pstep m1 m2 -> psstep (m1 .: σ) (m2 .: tau).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep, All2, pstep_refl.
  move=> p.
  apply: pstep_compat...
  apply: psstep_compat...
  exact: psstep_refl.
Qed.

Lemma pstep_compat_Beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using psstep_refl, psstep_compat.
  move=> p1 p2.
  apply: pstep_compat...
Qed.

Lemma pstep_iget1 ls ls' i m :
  All2 pstep ls ls' -> iget i ls m -> 
    exists m', iget i ls' m' /\ pstep m m'.
Proof with eauto using iget.
  move=> p.
  elim: p m i => {ls ls'}.
  move=> m i ig. inv ig.
  move=> m m' ls ls' p1 p2 ih m0 i ig. inv ig.
    exists m'...
    move: H3=> /ih [m'0 [ig p]].
    exists m'0...
Qed.

Lemma pstep_iget2 ls ls' i m' :
  All2 pstep ls ls' -> iget i ls' m' -> 
    exists m, iget i ls m /\ pstep m m'.
Proof with eauto using iget.
  move=> p.
  elim: p m' i => {ls ls'}.
  move=> m' i ig. inv ig.
  move=> m m' ls ls' p1 p2 ih m0 i ig. inv ig.
    exists m...
    move: H3=> /ih[m1 [ig p]].
    exists m1...
Qed.

Lemma pstep_spine h h' ls ls' :
  pstep h h' -> All2 pstep ls ls' -> pstep (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=> ls' h h' p1 p2. inv p2=> //=.
  move=> t t0 ih ls h h' p p'. inv p'=> //=.
  apply: ih=> //.
  exact: pstep_App.
Qed.

Lemma spine_Lam_Constr_False A m s i h ls :
  ~Lam A m s = spine' (Constr i h) ls.
Proof. elim: ls=> //=. Qed.

Lemma pstep_spine'_inv i h ls m :
  pstep (spine' (Constr i h) ls) m -> 
    exists h' ls', 
      m = spine' (Constr i h') ls' /\ 
      pstep h h' /\ 
      All2 pstep ls ls'.
Proof with eauto using pstep, All2, pstep_refl, All2_pstep_refl.
  elim: ls h m.
  move=> h m //= p. inv p.
    exists m'. exists nil...
  move=> t t0 ih h m //= p. inv p.
    move: H1=>/ih[h'[ls'[->[p1 p2]]]].
    exists h'. exists (n' :: ls')...
    exfalso.
    by apply: spine_Lam_Constr_False; eauto.
Qed.

Lemma pstep_spine'_congr i h1 h2 ms1 ms2 :
  pstep (spine' (Constr i h1) ms1) (spine' (Constr i h2) ms2) ->
    All2 pstep ms1 ms2.
Proof with eauto using All2.
  elim: ms1 ms2 h2 =>//=.
  destruct ms2=> //=...
    move=> h2 p. by inv p.
  move=> h ls ih ms2 h2.
    destruct ms2=> //= p. 
    inv p. exfalso. by apply: spine_Lam_Constr_False; eauto.
    inv p. 
      move: H2=>/ih tl...
      exfalso. by apply: spine_Lam_Constr_False; eauto.
Qed.

Lemma All2_pstep_append ls1 ls2 ls1' ls2' :
  All2 pstep ls1 ls2 -> All2 pstep ls1' ls2' ->
    All2 pstep (ls1 ++ ls1') (ls2 ++ ls2').
Proof with eauto using All2.
  move=> p. elim: p ls1' ls2'=> //={ls1 ls2}...
Qed.

Lemma All2_pstep_rev ls1 ls2 :
  All2 pstep ls1 ls2 -> All2 pstep (rev ls1) (rev ls2).
Proof with eauto using All2.
  elim=> //={ls1 ls2}...
  move=> m m' ls ls' p1 p2 p3.
    replace (m :: ls) with ([:: m] ++ ls) by eauto.
    replace (m' :: ls') with ([:: m'] ++ ls') by eauto.
    rewrite! rev_cat.
    apply All2_pstep_append...
Qed.

Lemma pstep_spine_inv i h ls m :
  pstep (spine (Constr i h) ls) m -> 
  exists h' ls', 
    m = spine (Constr i h') ls' /\ 
    pstep h h' /\ 
    All2 pstep ls ls'.
Proof with eauto using pstep, All2, pstep_refl, All2_pstep_refl.
  move=> p.
  move: (revK ls)=> e.
  rewrite <- e in p.
  rewrite spine_spine'_rev in p.
  move: p=> /pstep_spine'_inv[h'[ls'[->[p1 p2]]]].
  exists h'. exists (rev ls').
  rewrite spine_spine'_rev.
  rewrite revK.
  rewrite revK in p2.
  firstorder.
  apply All2_pstep_rev in p2.
  by rewrite revK in p2.
Qed.

Lemma pstep_spine_congr i h1 h2 ms1 ms2 :
  pstep (spine (Constr i h1) ms1) (spine (Constr i h2) ms2) ->
    All2 pstep ms1 ms2.
Proof with eauto using pstep, All2, pstep_refl, All2_pstep_refl.
  move=> p.
  move: (revK ms1)=> e1.
  move: (revK ms2)=> e2.
  rewrite <- e1 in p=>{e1}.
  rewrite <- e2 in p=>{e2}.
  rewrite! spine_spine'_rev in p.
  move: p=> /pstep_spine'_congr.
  rewrite! revK=> /All2_pstep_rev.
  by rewrite! revK.
Qed.

Lemma All2_diamond ls ls1 ls2 :
  All2 pstep ls ls1 ->
  All2 pstep ls ls2 ->
  All2 
    (fun m m1 => 
      forall m2, pstep m m2 -> 
        exists m', pstep m1 m' /\ pstep m2 m') ls ls1 ->
  exists ls', All2 pstep ls1 ls' /\ All2 pstep ls2 ls'.
Proof with eauto using All2.
  move=> p1 p2 h. move: ls2 p1 p2. elim: h=> {ls ls1}.
  move=> ls _ p. inv p.
    exists [::]...
  move=> m m' ls ls' f p ih ls2 p1 p2.
    inv p1.
    inv p2.
    move: H1=> /f[mx[p3 p4]].
    move: (ih _ H4 H5)=> [lsx[p5 p6]].
    exists (mx :: lsx)...
Qed.

Lemma pstep_diamond (m m1 m2 : term) (p : pstep m m1) :
  pstep m m2 -> exists m', pstep m1 m' /\ pstep m2 m'.
Proof with eauto 6 using 
  pstep, pstep_refl, All2, pstep_compat_Beta, pstep_spine.
Proof.
  move: m m1 p m2.
  apply: pstep_ind_nested.
  move=> x t p. inv p. exists (Var x)...
  move=> srt l m p. inv p. exists (Sort srt l)...
  move=> A A' n n' s pA ihA pN ihN m p. inv p.
    move: H3=> /ihA[Ax [pAx1 pAx2]].
    move: H4=> /ihN [nx [nx1 nx2]].
    exists (Lam Ax nx s)...
  move=> m m' n n' pM ihM pN ihN t p. inv p.
    move: H1=> /ihM [mx [pMx1 pM2]].
    move: H3=> /ihN [nx [pNx1 pNx2]].
    exists (App mx nx)...
    inv pM.
    have pLam : pstep (Lam A m0 s) (Lam A' m'0 s).
      by constructor.
    move: pLam=> /ihM [mx [pMx1 pMx2]].
    move: H3=> /ihN [nx [pNx1 pNx2]].
    inv pMx1; inv pMx2.
    exists (n'2.[nx/])...
  move=> A m m' n n' s pM ihM pN ihN t p. inv p.
    inv H1.
    move: H6=> /ihM [mx [pMx1 pMx2]].
    move: H3=> /ihN [nx [pNx1 pNx2]].
    exists (mx.[nx/])...
    move: H4=> /ihM [mx [pMx1 pMx2]].
    move: H5=> /ihN [nx [pNx1 pNx2]].
    exists (mx.[nx/])...
  move=> A A' B B' s pA ihA pB ihB t p. inv p.
    move: H3=> /ihA [Ax [pAx1 pAx2]].
    move: H4=> /ihB [Bx [pBx1 pBx2]].
    exists (Prod Ax Bx s)...
  move=> A A' B B' s pA ihA pB ihB t p. inv p.
    move: H3=> /ihA [Ax [pAx1 pAx2]].
    move: H4=> /ihB [Bx [pBx1 pBx2]].
    exists (Lolli Ax Bx s)...
  move=> A A' Cs Cs' s pA ihA pCs ihCs t p. inv p.
    move: H3=> /ihA [Ax [pAx1 pAx2]].
    move: (All2_diamond pCs H4 ihCs)=>[Csx[pCsx1 pCsx2]].
    exists (Ind Ax Csx s)...
  move=> i m m' pM ihM t p. inv p.
    move: H2=> /ihM [mx [pMx1 pMx2]].
    exists (Constr i mx)...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs t p. inv p.
    move: H2=> /ihM [mx [pMx1 pMx2]].
    move: H4=> /ihQ [Qx [pQx1 pQx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx [pFsx1 pFsx2]].
    exists (Case mx Qx Fsx)...
    move: (pstep_spine_inv pM)=>[hx [msx[e[pM0 pMs]]]]; subst.
    have pf : pstep (spine (Constr i m0) ms) (spine (Constr i m0) ms').
      apply: pstep_spine...
    move: pf=> /ihM[mx[pMx1 pMx2]].
    move: (pstep_spine_inv pMx1)=>[hx'[msx'[e[pHx pMsx]]]]; subst.
    move: pMx2=>/pstep_spine_congr=> pMs'.
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFxs1 pFxs2]].
    move: (pstep_iget1 pFxs2 H2)=> [Fx[ig pFx]].
    exists (spine Fx msx')...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs t p. inv p.
    move: H2=>/pstep_spine_inv[hx[mx[->[pM pMs']]]].
    move: (All2_diamond pMs pMs' ihMs)=>[mx'[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    exists (spine Fx mx')...
    move: H=> /spine_Constr_inj[e1[e2 e3]]; subst.
    move: (All2_diamond pMs H4 ihMs)=>[mx[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    move: (pstep_iget2 pFsx2 igFx)=>[Fx'[igFx' pFx']].
    move: (iget_iget igFx' H2)=>e; subst.
    exists (spine Fx mx)...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs t p. inv p.
    move: H2=> /ihM [mx [pMx1 pMx2]].
    move: H4=> /ihQ [Qx [pQx1 pQx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx [pFsx1 pFsx2]].
    exists (DCase mx Qx Fsx)...
    move: (pstep_spine_inv pM)=>[hx [msx[e[pM0 pMs]]]]; subst.
    have pf : pstep (spine (Constr i m0) ms) (spine (Constr i m0) ms').
      apply: pstep_spine...
    move: pf=> /ihM[mx[pMx1 pMx2]].
    move: (pstep_spine_inv pMx1)=>[hx'[msx'[e[pHx pMsx]]]]; subst.
    move: pMx2=>/pstep_spine_congr=> pMs'.
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFxs1 pFxs2]].
    move: (pstep_iget1 pFxs2 H2)=> [Fx[ig pFx]].
    exists (spine Fx msx')...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs t p. inv p.
    move: H2=>/pstep_spine_inv[hx[mx[->[pM pMs']]]].
    move: (All2_diamond pMs pMs' ihMs)=>[mx'[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    exists (spine Fx mx')...
    move: H=> /spine_Constr_inj[e1[e2 e3]]; subst.
    move: (All2_diamond pMs H4 ihMs)=>[mx[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    move: (pstep_iget2 pFsx2 igFx)=>[Fx'[igFx' pFx']].
    move: (iget_iget igFx' H2)=>e; subst.
    exists (spine Fx mx)...
  move=> A A' m m' pA ihA pM ihM t p. inv p.
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (Fix Ax mx)...
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (mx.[Fix Ax mx/])...
  move=> A A' m m' pA ihA pM ihM t p. inv p.
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (mx.[Fix Ax mx/])...
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (mx.[Fix Ax mx/])...
Qed.

Lemma strip m m1 m2 (p : pstep m m1) :
  red m m2 -> exists m', red m1 m' /\ pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=> rd. elim: rd m1 p=>{m2}...
  move=> y z rM ih /step_pstep p1 t /ih[x[r1 p2]].
  move: (pstep_diamond p1 p2)=>[w[pW1 pW2]].
  exists w. split...
  apply: star_trans; eauto.
  exact: pstep_red.
Qed.

Theorem confluence : confluent step.
Proof with eauto using step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r1 r2.
  elim: r1 z r2=>{y}.
  move=> z r.
    exists z...
  move=> y z1 r1 ih s z2 /ih[z3 r2].
    move: s=> /step_pstep p1 p2.
    move: (strip p1 r2)=>[mx[rMx1 rMx2]].
    exists mx...
    apply: star_trans...
    exact: pstep_red.
Qed.
Hint Resolve confluence.

Theorem church_rosser : CR step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.
Hint Resolve church_rosser.

Lemma red_Sort_inv s l A :
  red (Sort s l) A -> A = Sort s l.
Proof.
  elim; eauto.
  move=> y z r e st; subst.
  inv st; eauto.
Qed.

Lemma red_Prod_inv A B s x :
  red (Prod A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Prod A' B' s.
Proof.
  elim; eauto.
  move=> y z rd [A'[B'[rA[rB e]]]] st; subst.
  inv st.
  exists A'0. exists B'. firstorder.
    apply: star_trans; eauto.
    exact: star1.
  exists A'. exists B'0. firstorder.
    apply: star_trans; eauto.
    exact: star1.
Qed.

Lemma red_Lolli_inv A B s x :
  red (Lolli A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Lolli A' B' s.
Proof.
  elim; eauto.
  move=> y z rd [A'[B'[rA[rB e]]]] st; subst.
  inv st.
  exists A'0. exists B'. firstorder.
    apply: star_trans; eauto.
    exact: star1.
  exists A'. exists B'0. firstorder.
    apply: star_trans; eauto.
    exact: star1.
Qed.

Lemma red_Var_inv x y :
  red (Var x) y -> y = Var x.
Proof.
  elim; eauto.
  move=> y' z rd e s; subst. inv s.
Qed.

Lemma red_Lam_inv A m s n :
  red (Lam A m s) n ->
  exists A' m',
    red A A' /\ red m m' /\ n = Lam A' m' s.
Proof.
  elim.
  by exists A; exists m.
  move=> y z rd [A'[m'[rA[rM e]]]] st; subst.
  inv st.
  exists A'0. exists m'. repeat constructor; eauto using star.
  exists A'. exists m'0. repeat constructor; eauto using star.
Qed.

Lemma red_Ind_inv A Cs s n :
  red (Ind A Cs s) n ->
  exists A' Cs',
    red A A' /\ 
    star (One2 step) Cs Cs' /\ 
    n = Ind A' Cs' s.
Proof.
  elim.
  exists A. exists Cs. repeat constructor.
  move=> y z rd [A'[Cs'[rA[rCs e]]]] st; subst.
  inv st.
  exists A'0. exists Cs'. repeat constructor; eauto using star.
  exists A'. exists Cs'0. repeat constructor; eauto using star.
Qed.

Lemma red_Constr_inv i m n :
  red (Constr i m) n ->
  exists m',
    red m m' /\ n = Constr i m'.
Proof.
  elim.
  exists m. repeat constructor.
  move=> y z rd [m'[rM e]] st; subst.
  inv st.
  exists m'0. repeat constructor; eauto using star.
Qed.

Lemma Sort_inj s1 s2 l1 l2 :
  Sort s1 l1 === Sort s2 l2 ->
  s1 = s2 /\ l1 = l2.
Proof.
  move=> /church_rosser h. inv h.
  move: H=> /red_Sort_inv e; subst.
  move: H0=> /red_Sort_inv [->->]; eauto.
Qed.

Lemma Prod_inj A A' B B' s s' :
  Prod A B s === Prod A' B' s' ->
  A === A' /\ B === B' /\ s = s'.
Proof.
  move=> /church_rosser h. inv h.
  move: H=> /red_Prod_inv[Ax[Bx[rA[rB e]]]]; subst.
  move: H0=> /red_Prod_inv[Ax'[Bx'[rA'[rB' [e1 e2]]]]] ->; subst.
  firstorder; eauto using join_conv.
Qed.

Lemma Lolli_inj A A' B B' s s' :
  Lolli A B s === Lolli A' B' s' ->
  A === A' /\ B === B' /\ s = s'.
Proof.
  move=> /church_rosser h. inv h.
  move: H=> /red_Lolli_inv[Ax[Bx[rA[rB e]]]]; subst.
  move: H0=> /red_Lolli_inv[Ax'[Bx'[rA'[rB' [e1 e2]]]]] ->; subst.
  firstorder; eauto using join_conv.
Qed.

Lemma All2_cat (P : term -> term -> Prop) xs1 xs2 ys1 ys2 :
  All2 P xs1 ys1 ->
  All2 P xs2 ys2 ->
  All2 P (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  move=>a2. elim: a2 xs2 ys2=>//=.
  { move=> m m' ls ls' p a2 ih xs2 ys2 a2'.
    constructor; eauto. }
Qed.

Lemma All2_rev (P : term -> term -> Prop) xs ys :
  All2 P xs ys -> All2 P (rev xs) (rev ys).
Proof.
  elim.
  { rewrite /rev/catrev.
    constructor. }
  { move=> m m' ls ls' p a2 ih.
    replace (m :: ls) with ([::m] ++ ls) by eauto.
    replace (m' :: ls') with ([::m'] ++ ls') by eauto.
    rewrite! rev_cat.
    apply: All2_cat; eauto.
    rewrite /rev/catrev.
    repeat constructor; eauto. }
Qed.

Lemma All2_red_refl ms : All2 red ms ms.
Proof with eauto using All2.
  elim: ms...
Qed.

Lemma All2_conv_refl xs : All2 (conv step) xs xs.
Proof with eauto using All2.
  elim: xs...
Qed.

Lemma One2_step_All2_red xs ys :
  One2 step xs ys -> All2 red xs ys.
Proof with eauto using star1, All2, All2_red_refl.
  elim=>{xs ys}.
  { move=> m m' ls st... }
  { move=> m ls ls' o2 a2... }
Qed.

Lemma One2_step_All2_conv xs ys :
  One2 step xs ys -> All2 (conv step) xs ys.
Proof with eauto using conv1, All2, All2_conv_refl.
  elim=>{xs ys}.
  { move=> m m' ls st... }
  { move=> m ls ls' o2 a2... }
Qed.

Lemma All2_red_trans xs ys zs :
  All2 red xs ys ->
  All2 red ys zs ->
  All2 red xs zs.
Proof.
  move=> a2. elim: a2 zs=>{xs ys}.
  { move=> zs a2.
    inv a2.
    constructor. }
  { move=> m m' ls ls' rd a2 ih zs a2'.
    inv a2'.
    constructor; eauto.
    apply: star_trans; eauto. }
Qed.

Lemma All2_conv_trans xs ys zs :
  All2 (conv step) xs ys ->
  All2 (conv step) ys zs ->
  All2 (conv step) xs zs.
Proof.
  move=> a2. elim: a2 zs=>{xs ys}.
  { move=> zs a2.
    inv a2.
    constructor. }
  { move=> m m' ls ls' e a2 ih zs a2'.
    inv a2'.
    constructor; eauto.
    apply: conv_trans; eauto. }
Qed.

Lemma All2_conv_sym xs ys :
  All2 (conv step) xs ys -> All2 (conv step) ys xs.
Proof.
  elim.
  { constructor. }
  { move=> m m' ls ls' e a2 ih.
    constructor; eauto.
    apply: conv_sym; eauto. }
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
  { elim: xs; intros; constructor; eauto. }
  { move=> x z st a2 o2.
    apply One2_step_All2_conv in o2.
    apply: All2_conv_trans; eauto. }
Qed.

Lemma Ind_inj A A' Cs Cs' s s' :
  Ind A Cs s === Ind A' Cs' s' ->
  A === A' /\ 
  All2 (conv step) Cs Cs' /\
  s = s'.
Proof.
  move=>/church_rosser h. inv h.
  move: H=>/red_Ind_inv[Ax[Csx[rA[rCs e]]]]; subst.
  move: H0=>/red_Ind_inv[Ax'[Csx'[rA'[rCs' e']]]]; subst.
  inv e'.
  firstorder; eauto using join_conv.
  apply star_One2_step_All2_conv in rCs.
  apply star_One2_step_All2_conv in rCs'.
  apply: All2_conv_trans; eauto.
  apply: All2_conv_sym; eauto.
Qed.

Ltac red_inv m H :=
  match m with
  | Var    => apply red_Var_inv in H
  | Sort   => apply red_Sort_inv in H
  | Prod   => apply red_Prod_inv in H
  | Lolli  => apply red_Lolli_inv in H
  | Lam    => apply red_Lam_inv in H
  | Ind    => apply red_Ind_inv in H
  | Constr => apply red_Constr_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : red (?m _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
  end;
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  | [ H : value (App _ _) |- _ ] => inv H
  end; eauto.