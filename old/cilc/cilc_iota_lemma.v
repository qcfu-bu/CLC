From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion cilc_arity_spine
  cilc_validity cilc_typing_spine cilc_respine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma All2_conv_spine'_tail h xs ys :
  All2 (conv step) xs ys -> spine' h xs === spine' h ys.
Proof.
  elim=>//=.
  move=> m m' ls ls' e a2 ih.
  apply: conv_App; eauto.
Qed.

Lemma All2_conv_spine_tail h xs ys :
  All2 (conv step) xs ys -> spine h xs === spine h ys.
Proof.
  move=>/All2_rev/(All2_conv_spine'_tail h).
  rewrite! spine_spine'_rev; eauto.
Qed.

Lemma eq_spine'_Ind A A' Cs Cs' s s' ms ms' :
  spine' (Ind A Cs s) ms = spine' (Ind A' Cs' s') ms' ->
  Ind A Cs s = Ind A' Cs' s' /\ ms = ms'.
Proof.
  elim: ms A A' Cs Cs' s s' ms'; intros; simpl in H.
  { destruct ms'; simpl in H; try discriminate; eauto. }
  { destruct ms'; simpl in H0; try discriminate; eauto.
    inv H0.
    move: (H _ _ _ _ _ _ _ H2)=>[->->].
    eauto. }
Qed.

Lemma step_spine'_Var x ms n:
  step (spine' (Var x) ms) n ->
  exists ms', 
    n = spine' (Var x) ms' /\
    One2 step ms ms'.
Proof with eauto using One2.
  elim: ms x n; simpl; intros.
  inv H.
  inv H0.
  { move: (H _ _ H4)=>[ms'[-> o2]].
    exists (a :: ms')... }
  { exists (n' :: l)... }
  { exfalso; solve_spine'... }
Qed.

Lemma step_spine'_Ind A Cs s ms n :
  step (spine' (Ind A Cs s) ms) n ->
  exists A' Cs' ms', 
    n = spine' (Ind A' Cs' s) ms' /\
    ((step (Ind A Cs s) (Ind A' Cs' s) /\ ms = ms') \/ 
      (Ind A Cs s = Ind A' Cs' s /\ One2 step ms ms')).
Proof.
  elim: ms A Cs s n; intros.
  { simpl in H. inv H.
    { exists A'.
      exists Cs.
      exists nil. 
      split; simpl; eauto.
      left; repeat constructor; eauto. }
    { exists A.
      exists Cs'.
      exists nil.
      split; simpl; eauto.
      left; repeat constructor; eauto. } }
  { simpl in H0. inv H0.
    { move: (H _ _ _ _ H4)=>[A'[Cs'[ms'[e[[h1 h2]|[h1 h2]]]]]]; subst.
      { exists A'.
        exists Cs'.
        exists (a :: ms').
        split; simpl; eauto. }
      { exists A.
        exists Cs.
        exists (a :: ms').
        split; simpl.
        rewrite h1; eauto.
        right; repeat constructor; eauto. } }
    { exists A.
      exists Cs.
      exists (n' :: l).
      split; simpl; eauto.
      right; repeat constructor; eauto. }
    { destruct l; try discriminate. } }
Qed.

Lemma red_spine'_Var x ms n :
  red (spine' (Var x) ms) n ->
  exists ms', 
    n = spine' (Var x) ms' /\
    All2 red ms ms'.
Proof with eauto using All2, All2_red_refl.
  move e:(spine' (Var x) ms)=>m rd.
  elim: rd x ms e=>{n}; intros; subst.
  { exists ms... }
  { have e : spine' (Var x) ms = spine' (Var x) ms by eauto.
    move: (H0 _ _ e)=>[ms'[e' a2]]; subst.
    move: (step_spine'_Var H1)=>[msx[ez o2]].
    move: o2=>/One2_step_All2_red a2x.
    exists msx.
    split; eauto.
    apply: All2_red_trans; eauto. }
Qed.

Lemma red_spine'_Ind A Cs s ms n :
  red (spine' (Ind A Cs s) ms) n ->
  exists A' Cs' ms',
    n = (spine' (Ind A' Cs' s) ms') /\ 
    red (Ind A Cs s) (Ind A' Cs' s) /\
    All2 red ms ms'.
Proof with eauto using All2, All2_red_refl.
  move e:(spine' (Ind A Cs s) ms)=>m rd.
  elim: rd A Cs s ms e=>{n}; intros; subst.
  { exists A.
    exists Cs.
    exists ms.
    repeat split... }
  { have e : spine' (Ind A Cs s) ms = spine' (Ind A Cs s) ms.
      by eauto.
    move: (H0 _ _ _ _ e)=>{e}[A'[Cs'[ms'[e[rd a2]]]]]; subst.
    move: (step_spine'_Ind H1)=>[Ax[Csx[msx[e[[h1 h2]|[h1 h2]]]]]]; 
    subst.
    { exists Ax.
      exists Csx.
      exists msx.
      repeat split; eauto.
      apply: star_trans; eauto. 
      apply: star1; eauto. }
    { exists Ax.
      exists Csx.
      exists msx.
      split; eauto.
      rewrite<-h1; split; eauto.
      apply One2_step_All2_red in h2.
      apply: All2_red_trans... } }
Qed.

Lemma red_spine_Var x ms n :
  red (spine (Var x) ms) n ->
  exists ms', 
    n = spine (Var x) ms' /\
    All2 red ms ms'.
Proof.
  rewrite spine_spine'_rev=> rd.
  move: (red_spine'_Var rd); firstorder.
  exists (rev x0).
  split.
  { rewrite spine_spine'_rev.
    rewrite revK; eauto. }
  { apply All2_rev in H0.
    rewrite revK in H0; eauto. }
Qed.

Lemma red_spine_Ind A Cs s ms n :
  red (spine (Ind A Cs s) ms) n ->
  exists A' Cs' ms',
    n = (spine (Ind A' Cs' s) ms') /\ 
    red (Ind A Cs s) (Ind A' Cs' s) /\
    All2 red ms ms'.
Proof.
  rewrite spine_spine'_rev=> rd.
  move: (red_spine'_Ind rd); firstorder.
  exists x.
  exists x0.
  exists (rev x1).
  repeat split; eauto.
  { rewrite spine_spine'_rev.
    rewrite revK; eauto. }
  { apply All2_rev in H1.
    rewrite revK in H1; eauto. }
Qed.

Lemma conv_spine'_Ind A A' Cs Cs' s s' ms ms' :
  spine' (Ind A Cs s) ms === spine' (Ind A' Cs' s') ms' ->
  Ind A Cs s === Ind A' Cs' s' /\ 
  All2 (conv step) ms ms'.
Proof.
  move=> /church_rosser h. inv h.
  move: (red_spine'_Ind H)=>{H}[A1[Cs1[ms1[e1[rd1 a1]]]]].
  move: (red_spine'_Ind H0)=>{H0}[A2[Cs2[ms2[e2[rd2 a2]]]]]; subst.
  move: (eq_spine'_Ind e2)=>[e3 e4]; subst.
  split.
  { rewrite e3 in rd1.
    apply: conv_trans.
    apply: star_conv.
    apply: rd1.
    apply: conv_sym.
    apply: star_conv.
    eauto. }
  { apply: All2_conv_trans.
    { apply: All2_red_conv; eauto. }
    { apply: All2_conv_sym.
      apply: All2_red_conv; eauto. } }
Qed.

Lemma sub_spine'_Ind A A' Cs Cs' s s' ms ms' :
  spine' (Ind A Cs s) ms <: spine' (Ind A' Cs' s') ms' ->
  Ind A Cs s === Ind A' Cs' s' /\
  All2 (conv step) ms ms'.
Proof.
  move=>[X Y []]; intros.
  { apply: conv_spine'_Ind.
    apply: conv_trans.
    apply: c.
    apply: c0. }
  { move: c=>/church_rosser h. inv h.
    move: H0=>/red_Sort_inv e; subst.
    move: H=>/red_spine'_Ind[Ax[Csx[msx[e _]]]].
    exfalso; solve_spine'. }
  { move: c=>/church_rosser h. inv h.
    move: H0=>/red_Arrow_inv[Ax[Bx[_[_ e]]]]; subst.
    move: H=>/red_spine'_Ind[Ay[Csy[msy[e _]]]].
    exfalso; solve_spine'. }
  { move: c=>/church_rosser h. inv h.
    move: H0=>/red_Lolli_inv[Ax[Bx[_[_ e]]]]; subst.
    move: H=>/red_spine'_Ind[Ay[Csy[msy[e _]]]].
    exfalso; solve_spine'. }
Qed.

Lemma sub_spine_Ind A A' Cs Cs' s s' ms ms' :
  spine (Ind A Cs s) ms <: spine (Ind A' Cs' s') ms' ->
  Ind A Cs s === Ind A' Cs' s' /\
  All2 (conv step) ms ms'.
Proof.
  rewrite! spine_spine'_rev=>/sub_spine'_Ind[e h].
  split; eauto.
  apply All2_rev in h.
  rewrite !revK in h; eauto.
Qed.

Ltac solve_sub_spine_trans H1 H2 :=
  let x := fresh "x" in
  let h := fresh "h" in
  have x := conv_trans _ H1 H2;
  have h := church_rosser x; inv h;
  match goal with
  | [ H1 : red (Arrow _ _ _) ?x,
      H2 : red (spine (Ind _ _ _) _) ?x |- _ ] =>
    move: H1=>/red_Arrow_inv; firstorder; subst;
    move: H2=>/red_spine_Ind; firstorder; subst;
    solve_spine
  | [ H1 : red (Lolli _ _ _) ?x,
      H2 : red (spine (Ind _ _ _) _) ?x |- _ ] =>
    move: H1=>/red_Lolli_inv; firstorder; subst;
    move: H2=>/red_spine_Ind; firstorder; subst;
    solve_spine
  end.

Ltac solve_sub_spine' :=
  match goal with
  | [ H : spine (Ind _ _ _ ) _ === Arrow _ _ _ |- _ ] =>
    let h := fresh "h" in
    have h := church_rosser H; inv h
  | [ H : Arrow _ _ _ === spine (Ind _ _ _ ) _ |- _ ] =>
    let h := fresh "h" in
    have h := church_rosser H; inv h
  | [ H : Lolli _ _ _ === spine (Ind _ _ _ ) _ |- _ ] =>
    let h := fresh "h" in
    have h := church_rosser H; inv h
  | [ H : spine (Ind _ _ _ ) _ === Lolli _ _ _ |- _ ] =>
    let h := fresh "h" in
    have h := church_rosser H; inv h
  | _ => solve_conv
  end;
  match goal with
  | [ H1 : red (Arrow _ _ _) ?x,
      H2 : red (spine (Ind _ _ _) _) ?x |- _ ] =>
    move: H1=>/red_Arrow_inv; firstorder; subst;
    move: H2=>/red_spine_Ind; firstorder; subst;
    solve_spine
  | [ H1 : red (Lolli _ _ _) ?x,
      H2 : red (spine (Ind _ _ _) _) ?x |- _ ] =>
    move: H1=>/red_Lolli_inv; firstorder; subst;
    move: H2=>/red_spine_Ind; firstorder; subst;
    solve_spine
  end.

Ltac solve_sub_spine :=
  match goal with
  | [ H : spine (Ind _ _ _ ) _ <: Arrow _ _ _ |- _ ] =>
    move: H=>[_ _ []]; intros
  | [ H : Arrow _ _ _ <: spine (Ind _ _ _ ) _ |- _ ] =>
    move: H=>[_ _ []]; intros
  | [ H : spine (Ind _ _ _ ) _ <: Lolli _ _ _ |- _ ] =>
    move: H=>[_ _ []]; intros
  | [ H : Lolli _ _ _ <: spine (Ind _ _ _ ) _ |- _ ] =>
    move: H=>[_ _ []]; intros
  | _ => solve_sub
  end;
  try match goal with
  | [ H1 : spine (Ind _ _ _) _ === ?x,
      H2 : ?x === Arrow _ _ _ |- _ ] =>
    solve_sub_spine_trans H1 H2
  | [ H1 : spine (Ind _ _ _) _ === ?x,
      H2 : ?x === Lolli _ _ _ |- _ ] =>
    solve_sub_spine_trans H1 H2
  | [ H1 : ?x === spine (Ind _ _ _) _,
      H2 : Arrow _ _ _ === ?x |- _ ] =>
    solve_sub_spine_trans H2 H1
  | [ H1 : ?x === spine (Ind _ _ _) _,
      H2 : Lolli _ _ _ === ?x |- _ ] =>
    solve_sub_spine_trans H2 H1
  | _ => solve_sub_spine'
  end.

Lemma typing_spine_Ind_Ind Γ A1 A2 Cs1 Cs2 s1 s2 ms1 ms2 ms :
  typing_spine Γ 
    (spine (Ind A1 Cs1 s1) ms1) ms (spine (Ind A2 Cs2 s2) ms2) ->
  Ind A1 Cs1 s1 === Ind A2 Cs2 s2.
Proof.
  move e1:(spine (Ind A1 Cs1 s1) ms1)=> n1.
  move e2:(spine (Ind A2 Cs2 s2) ms2)=> n2 sp.
  elim: sp A1 A2 Cs1 Cs2 s1 s2 ms1 ms2 e1 e2=>{Γ n1 n2 ms}; 
  intros; subst; try solve [ exfalso; solve_sub_spine ].
  move: H0=>/sub_spine_Ind[h _]; eauto.
Qed.

Lemma typing_spine_active_Ind Γ I C A A' Cs Cs' s s' ms ms' n :
  active n C ->
  typing_spine Γ C.[I] ms (spine (Ind A' Cs' s') ms') ->
  I n = Ind A Cs s -> I n === Ind A' Cs' s'.
Proof.
  move=> a. elim: a Γ I A A' Cs Cs' s' ms ms'=>{C}; intros.
  { rewrite spine_subst in H0; simpl in H0.
    rewrite H1 in H0.
    rewrite H1.
    apply: typing_spine_Ind_Ind; eauto. }
  { simpl in H3. inv H3; try solve [exfalso; solve_sub_spine].
    { move: H6=>/sub_Lolli_inv; firstorder; subst.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs s.
        asimpl; eauto.
      move: (u_Lolli_inv H7)=>[sx[l1[l2[tyA[tyB _]]]]].
      have mg : merge Γ1 Γ1 Γ1.
        by apply: merge_pure.
      move: (merge_re_re H9)=>[e1 e2].
      move: (substitutionU tyB H8 H5 mg)=>//={}tyB.
      have {}tyB : [ re Γ1 |- B0.[hd/] :- sx @ l1 ].
        rewrite<-pure_re; eauto.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H10 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. }
    { move: H5=>/sub_Lolli_inv; firstorder; subst.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs s.
        asimpl; eauto.
      move: (l_Lolli_inv H6)=>[sx[l1[l2[tyA[tyB _]]]]].
      move: (merge_re_re H8)=>[e1 e2].
      move: (substitutionN tyB H7)=>//={}tyB.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H9 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. } }
  { simpl in H2. inv H2; try solve [exfalso; solve_sub_spine].
    { move: H5=>/sub_Lolli_inv; firstorder; subst.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs s.
        asimpl; eauto.
      move: (u_Lolli_inv H6)=>[sx[l1[l2[tyA[tyB _]]]]].
      have mg : merge Γ1 Γ1 Γ1.
        by apply: merge_pure.
      move: (merge_re_re H8)=>[e1 e2].
      move: (substitutionU tyB H7 H4 mg)=>//={}tyB.
      have {}tyB : [ re Γ1 |- B0.[hd/] :- sx @ l1 ].
        rewrite<-pure_re; eauto.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H9 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. }
    { move: H4=>/sub_Lolli_inv; firstorder; subst.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs s.
        asimpl; eauto.
      move: (l_Lolli_inv H5)=>[sx[l1[l2[tyA[tyB _]]]]].
      move: (merge_re_re H7)=>[e1 e2].
      move: (substitutionN tyB H6)=>//={}tyB.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H8 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. } }
Qed.

Lemma typing_spine_constr_Ind Γ I C A A' Cs Cs' s s' ms ms' n :
  constr n s C ->
  typing_spine Γ C.[I] ms (spine (Ind A' Cs' s') ms') ->
  I n = Ind A Cs s -> I n === Ind A' Cs' s'.
Proof.
  move=>c. elim: c Γ I A A' Cs Cs' s' ms ms'=>{s C}; intros.
  { rewrite spine_subst in H0; simpl in H0.
    rewrite H1 in H0.
    rewrite H1.
    apply: typing_spine_Ind_Ind; eauto. }
  { simpl in H3. inv H3; try solve [exfalso; solve_sub_spine].
    { move: H6=>/sub_Arrow_inv; firstorder.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs U.
        asimpl; eauto.
      move: (u_Arrow_inv H7)=>[s[l1[l2[tyA[tyB _]]]]].
      have mg : merge Γ1 Γ1 Γ1.
        by apply: merge_pure.
      move: (merge_re_re H9)=>[e1 e2].
      move: (substitutionU tyB H8 H5 mg)=>//={}tyB.
      have {}tyB : [ re Γ1 |- B0.[hd/] :- s @ l1 ].
        rewrite<-pure_re; eauto.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H10 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. }
    { move: H5=>/sub_Arrow_inv; firstorder. 
      discriminate. } }
  { simpl in H2. inv H2; try solve [exfalso; solve_sub_spine].
    { move: H5=>/sub_Arrow_inv; firstorder.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs U.
        asimpl; eauto.
      move: (u_Arrow_inv H6)=>[s[l1[l2[tyA[tyB _]]]]].
      have mg : merge Γ1 Γ1 Γ1.
        by apply: merge_pure.
      move: (merge_re_re H8)=>[e1 e2].
      move: (substitutionU tyB H7 H4 mg)=>//={}tyB.
      have {}tyB : [ re Γ1 |- B0.[hd/] :- s @ l1 ].
        rewrite<-pure_re; eauto.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H9 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. }
    { move: H4=>/sub_Arrow_inv; firstorder.
      discriminate. } }
  { simpl in H3. inv H3; try solve [exfalso; solve_sub_spine].
    { move: H6=>/sub_Arrow_inv; firstorder.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs L.
        asimpl; eauto.
      move: (u_Arrow_inv H7)=>[s[l1[l2[tyA[tyB _]]]]].
      have mg : merge Γ1 Γ1 Γ1.
        by apply: merge_pure.
      move: (merge_re_re H9)=>[e1 e2].
      move: (substitutionU tyB H8 H5 mg)=>//={}tyB.
      have {}tyB : [ re Γ1 |- B0.[hd/] :- s @ l1 ].
        rewrite<-pure_re; eauto.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H10 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. }
    { move: H5=>/sub_Arrow_inv; firstorder. 
      discriminate. } }
  { simpl in H2. inv H2; try solve [exfalso; solve_sub_spine].
    { move: H5=>/sub_Arrow_inv; firstorder.
      discriminate. }
    { move: H4=>/sub_Arrow_inv; firstorder.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs L.
        asimpl; eauto.
      move: (l_Arrow_inv H5)=>[s[l1[l2[tyA[tyB _]]]]].
      move: (merge_re_re H7)=>[e1 e2].
      move: (substitutionN tyB H6)=>//={}tyB.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H8 sb tyB)=>tySp.
      move: (typing_spine_active_Ind H0 tySp e); eauto. } }
  { simpl in H2. inv H2; try solve [exfalso; solve_sub_spine].
    { move: H5=>/sub_Arrow_inv; firstorder.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs L.
        asimpl; eauto.
      move: (u_Arrow_inv H6)=>[s[l1[l2[tyA[tyB _]]]]].
      have mg : merge Γ1 Γ1 Γ1.
        by apply: merge_pure.
      move: (merge_re_re H8)=>[e1 e2].
      move: (substitutionU tyB H7 H4 mg)=>//={}tyB.
      have {}tyB : [ re Γ1 |- B0.[hd/] :- s @ l1 ].
        rewrite<-pure_re; eauto.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H9 sb tyB)=>tySp.
      move: (H1 Γ2 (hd .: I) A0 A' Cs Cs' s' tl ms' tySp); eauto. }
    { move: H4=>/sub_Arrow_inv; firstorder.
      discriminate. } }
  { simpl in H1. inv H1; try solve [exfalso; solve_sub_spine].
    { move: H4=>/sub_Arrow_inv; firstorder.
      discriminate. }
    { move: H3=>/sub_Arrow_inv; firstorder.
      have sb : B.[up I].[hd/] <: B0.[hd/].
        apply: sub_subst; eauto.
      asimpl in sb.
      have e : (hd .: I) x.+1 = Ind A0 Cs L.
        asimpl; eauto.
      move: (l_Arrow_inv H4)=>[s[l1[l2[tyA[tyB _]]]]].
      move: (merge_re_re H6)=>[e1 e2].
      move: (substitutionN tyB H5)=>//={}tyB.
      rewrite e1 in tyB. rewrite<-e2 in tyB.
      move: (typing_spine_strengthen H7 sb tyB)=>tySp.
      move: (typing_spine_active_Ind H0 tySp e); eauto. } }
Qed.

Lemma typing_spine_Ind_Q1 Γ A Q Cs ms1 ms2 ms s t l :
  typing_spine Γ (spine (Ind A Cs s) ms1) ms (spine (Ind A Cs s) ms2) ->
  [ re Γ |- spine Q ms2 :- t @ l ] ->
  typing_spine Γ (spine Q ms1) ms (spine Q ms2).
Proof.
  move e1:(spine (Ind A Cs s) ms1)=> n1.
  move e2:(spine (Ind A Cs s) ms2)=> n2 sp.
  elim: sp A Q Cs ms1 ms2 s t l e1 e2=>{Γ ms n1 n2}; 
  intros; subst; try solve [exfalso; solve_sub_spine].
  apply: typing_spine_nil; eauto.
  2:{ rewrite<-pure_re in H2; eauto. }
  move: H0=>/sub_spine_Ind[_ a2].
  apply: conv_sub.
  apply: All2_conv_spine_tail; eauto.
Qed.

Lemma typing_spine_Ind_Q2 Γ A Q Cs ms1 ms2 ms c s l :
  typing_spine Γ (spine (Ind A Cs U) ms1) ms (spine (Ind A Cs U) ms2) ->
  [ re Γ |- spine Q ms2 :- Arrow (spine (Ind A Cs U) ms2) (s @ l) U ] ->
  [ re Γ |- c :- spine (Ind A Cs U) ms1 ] ->
  typing_spine Γ (App (spine Q ms1) c) ms (App (spine Q ms2) (spine c ms)).
Proof.
  move e1:(spine (Ind A Cs U) ms1)=> n1.
  move e2:(spine (Ind A Cs U) ms2)=> n2 sp.
  elim: sp A Q Cs ms1 ms2 c s l e1 e2=>{Γ ms n1 n2}; 
  intros; subst; try solve [exfalso; solve_sub_spine]; simpl.
  rewrite<-pure_re in H2; eauto.
  rewrite<-pure_re in H3; eauto.
  have mg := merge_pure H.
  have tyC : [ Γ |- c :- spine (Ind A0 Cs U) ms2 ].
    apply: s_Conv; eauto.
    rewrite<-pure_re; eauto.
  have //=h1 := u_Arrow_App H H2 tyC mg.
  apply: typing_spine_nil; eauto.
  move: H0=>/sub_spine_Ind[_ a2].
  apply: conv_sub.
  apply: conv_App; eauto.
  apply: All2_conv_spine_tail; eauto.
Qed.

Lemma typing_spine_active Γ A Cs C I Q ms1 ms2 s t2 t3 l2 l3 n :
  active n C ->
  typing_spine Γ C.[I] ms1 (spine (I n) ms2) ->
  (I n = Ind A Cs L) ->
  (forall x, ~I n = Var x) ->
  [ re Γ |- C.[I] :- s @ l3 ] ->
  [ re Γ |- Ind A Cs L :- A ] ->
  [ re Γ |- Q :- arity1 t2 A ] ->
  [ re Γ |- spine Q ms2 :- t3 @ l2 ] ->
  typing_spine Γ (respine Q C.[I]) ms1 (spine Q ms2).
Proof.
  move=>a. 
  elim: a Γ A Cs I Q ms1 ms2 s t2 t3 l2 l3; simpl; intros.
  { rewrite spine_subst; simpl.
    rewrite H1.
    rewrite respine_spine_Ind.
    rewrite spine_subst in H0; simpl in H0.
    rewrite H1 in H0.
    apply: typing_spine_Ind_Q1; eauto. }
  { rewrite H4 in H3. 
    inv H3; try solve[exfalso; solve_sub_spine].
    { apply sub_Lolli_inv in H11; firstorder; subst.
      move: (merge_re_re H14)=>[e1 e2].
      move: (u_Lolli_inv H12); firstorder.
      move: (u_Lolli_inv H6); firstorder.
      move: (s_Ind_inv H7); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H4; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H4. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H4. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@active_respine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 h4); firstorder.
      simpl in H27.
      rewrite<-e1 in H27.
      rewrite<-pure_re in H27; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H13. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite active_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Lolli_inv in H10; firstorder; subst.
      move: (merge_re_re H13)=>[e1 e2].
      move: (l_Lolli_inv H11); firstorder.
      move: (l_Lolli_inv H6); firstorder.
      move: (s_Ind_inv H7); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H4; asimpl; eauto. }
      have h2 : [ +n re Γ |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H4. apply: eweakeningN; eauto. }
      have h3 : [ +n re Γ |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningN; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h5 : pure (re Γ2).
      { apply: re_pure. }
      have h6 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { move: (substitutionN H19 H12); asimpl.
        rewrite<-e2; eauto. }
      have h7 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h7.
      have h8 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2. rewrite<-e1.
        move: (substitutionN H16 H12); eauto. }
      have h9 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H4. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@active_respine (A1 +l Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 H19); firstorder.
      simpl in H26.
      rewrite<-e1 in H26.
      apply: typing_spine_l_Lolli_cons.
      3:{ apply: H12. }
      { apply: conv_sub.
        apply: conv_Lolli; eauto. }
      2:{ eauto. }
      { apply: l_Lolli_max; eauto.
        apply: re_pure. }
      { erewrite active_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } } }
  { rewrite H3 in H2. 
    inv H2; try solve[exfalso; solve_sub_spine].
    { apply sub_Lolli_inv in H10; firstorder; subst.
      move: (merge_re_re H13)=>[e1 e2].
      move: (u_Lolli_inv H11); firstorder.
      move: (u_Lolli_inv H5); firstorder.
      move: (s_Ind_inv H6); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H3; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H3. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H3. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@active_respine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 h4); firstorder.
      simpl in H26.
      rewrite<-e1 in H26.
      rewrite<-pure_re in H26; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H12. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite active_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Lolli_inv in H9; firstorder; subst.
      move: (merge_re_re H12)=>[e1 e2].
      move: (l_Lolli_inv H10); firstorder.
      move: (l_Lolli_inv H5); firstorder.
      move: (s_Ind_inv H6); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H3; asimpl; eauto. }
      have h2 : [ +n re Γ |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H3. apply: eweakeningN; eauto. }
      have h3 : [ +n re Γ |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningN; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h5 : pure (re Γ2).
      { apply: re_pure. }
      have h6 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { move: (substitutionN H18 H11); asimpl.
        rewrite<-e2; eauto. }
      have h7 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h7.
      have h8 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2. rewrite<-e1.
        move: (substitutionN H15 H11); eauto. }
      have h9 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H3. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@active_respine (A1 +l Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 H18); firstorder.
      simpl in H25.
      rewrite<-e1 in H25.
      apply: typing_spine_l_Lolli_cons.
      3:{ apply: H11. }
      { apply: conv_sub.
        apply: conv_Lolli; eauto. }
      2:{ eauto. }
      { apply: l_Lolli_max; eauto.
        apply: re_pure. }
      { erewrite active_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } } }
Qed.

Lemma typing_spine_constr1 Γ A Cs C I Q ms1 ms2 r s t2 t3 l2 l3 n :
  constr n s C ->
  typing_spine Γ C.[I] ms1 (spine (I n) ms2) ->
  (I n = Ind A Cs s) ->
  (forall x, ~I n = Var x) ->
  [ re Γ |- C.[I] :- r @ l3 ] ->
  [ re Γ |- Ind A Cs s :- A ] ->
  [ re Γ |- Q :- arity1 t2 A ] ->
  [ re Γ |- spine Q ms2 :- t3 @ l2 ] ->
  typing_spine Γ (respine Q C.[I]) ms1 (spine Q ms2).
Proof.
  move=>c. 
  elim: c Γ A Cs I Q ms1 ms2 r t2 t3 l2 l3; simpl; intros.
  { rewrite spine_subst; simpl.
    rewrite H1.
    rewrite respine_spine_Ind.
    rewrite spine_subst in H0; simpl in H0.
    rewrite H1 in H0.
    apply: typing_spine_Ind_Q1; eauto. }
  { rewrite H4 in H3. 
    inv H3; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H11; firstorder.
      move: (merge_re_re H14)=>[e1 e2].
      move: (u_Arrow_inv H12); firstorder.
      move: (u_Arrow_inv H6); firstorder.
      move: (s_Ind_inv H7); firstorder.
      have a : arity U A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
      { asimpl. rewrite H4; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H4. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H4. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@constr_respine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 U t2 x4 H0 a h1 h2 h3 h4); firstorder.
      simpl in H28.
      rewrite<-e1 in H28.
      rewrite<-pure_re in H28; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H13. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite constr_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Arrow_inv in H10; firstorder; discriminate. } }
  { rewrite H3 in H2. 
    inv H2; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H10; firstorder.
      move: (merge_re_re H13)=>[e1 e2].
      move: (u_Arrow_inv H11); firstorder.
      move: (u_Arrow_inv H5); firstorder.
      move: (s_Ind_inv H6); firstorder.
      have a : arity U A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
      { asimpl. rewrite H3; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H3. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H3. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@constr_respine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 U t2 x4 H0 a h1 h2 h3 h4); firstorder.
      simpl in H27.
      rewrite<-e1 in H27.
      rewrite<-pure_re in H27; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H12. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite constr_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Arrow_inv in H9; firstorder; discriminate. } }
  { rewrite H4 in H3. 
    inv H3; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H11; firstorder.
      move: (merge_re_re H14)=>[e1 e2].
      move: (u_Arrow_inv H12); firstorder.
      move: (u_Arrow_inv H6); firstorder.
      move: (s_Ind_inv H7); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H4; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H4. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H4. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@constr_respine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 h4); firstorder.
      simpl in H28.
      rewrite<-e1 in H28.
      rewrite<-pure_re in H28; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H13. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite constr_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Arrow_inv in H10; firstorder; discriminate. } }
  { rewrite H3 in H2. 
    inv H2; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H10; firstorder; discriminate. }
    { apply sub_Arrow_inv in H9; firstorder.
      move: (merge_re_re H12)=>[e1 e2].
      move: (l_Arrow_inv H10); firstorder.
      move: (l_Arrow_inv H5); firstorder.
      move: (s_Ind_inv H6); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H3; asimpl; eauto. }
      have h2 : [ +n re Γ |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H3. apply: eweakeningN; eauto. }
      have h3 : [ +n re Γ |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningN; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h5 : pure (re Γ2).
      { apply: re_pure. }
      have h6: [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { rewrite e2.
        move: (substitutionN H19 H11); asimpl; eauto. }
      have h7 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h7.
      have h8 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2. rewrite<-e1.
        move: (substitutionN H16 H11)=>//=. }
      have h9 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H3. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@active_respine (A1 +l Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 H19); firstorder.
      simpl in H26.
      rewrite<-e1 in H26.
      apply: typing_spine_l_Lolli_cons.
      3:{ apply: H11. }
      { apply: conv_sub.
        apply: conv_Lolli; eauto. }
      2:{ eauto. }
      { apply: l_Lolli_max; eauto.
        apply: re_pure. }
      { erewrite active_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: typing_spine_active; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } } }
  { rewrite H3 in H2. 
    inv H2; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H10; firstorder.
      move: (merge_re_re H13)=>[e1 e2].
      move: (u_Arrow_inv H11); firstorder.
      move: (u_Arrow_inv H5); firstorder.
      move: (s_Ind_inv H6); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H3; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H3. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H3. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@constr_respine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 h4); firstorder.
      simpl in H27.
      rewrite<-e1 in H27.
      rewrite<-pure_re in H27; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H12. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite constr_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Arrow_inv in H9; firstorder; discriminate. } }
  { rewrite H2 in H1. 
    inv H1; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H9; firstorder; discriminate. }
    { apply sub_Arrow_inv in H8; firstorder.
      move: (merge_re_re H11)=>[e1 e2].
      move: (l_Arrow_inv H9); firstorder.
      move: (l_Arrow_inv H4); firstorder.
      move: (s_Ind_inv H5); firstorder.
      have a : arity L A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L.
      { asimpl. rewrite H2; asimpl; eauto. }
      have h2 : [ +n re Γ |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H2. apply: eweakeningN; eauto. }
      have h3 : [ +n re Γ |- Q.[ren (+1)] :- (arity1 t2 A0).[ren (+1)]].
      { asimpl. apply: eweakeningN; eauto. }
      erewrite arity1_subst in h3; eauto.
      have h4 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h5 : pure (re Γ2).
      { apply: re_pure. }
      have h6: [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { rewrite e2.
        move: (substitutionN H18 H10); asimpl; eauto. }
      have h7 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h7.
      have h8 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2. rewrite<-e1.
        move: (substitutionN H15 H10)=>//=. }
      have h9 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H2. apply: typing_spine_strengthen; eauto. }
      pose proof 
      (@active_respine (A1 +l Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B x.+1 x3 L t2 x4 H0 a h1 h2 h3 H18); firstorder.
      simpl in H25.
      rewrite<-e1 in H25.
      apply: typing_spine_l_Lolli_cons.
      3:{ apply: H10. }
      { apply: conv_sub.
        apply: conv_Lolli; eauto. }
      2:{ eauto. }
      { apply: l_Lolli_max; eauto.
        apply: re_pure. }
      { erewrite active_respine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: typing_spine_active; eauto.
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } } }
Qed.

Lemma typing_spine_constr2 Γ A Cs C I Q ms1 ms2 c s t1 t2 l1 l2 n :
  constr n U C ->
  typing_spine Γ C.[I] ms1 (spine (I n) ms2) ->
  (I n = Ind A Cs U) ->
  (forall x, ~I n = Var x) ->
  [ re Γ |- C.[I] :- t1 @ l1 ] ->
  [ re Γ |- c :- C.[I] ] ->
  [ re Γ |- Ind A Cs U :- A ] ->
  [ re Γ |- Q :- arity2 s (Ind A Cs U) A ] ->
  [ re Γ |- spine Q ms2 :- Arrow (spine (Ind A Cs U) ms2) (t2 @ l2) U ] ->
  typing_spine Γ 
    (drespine Q c C.[I]) ms1 (App (spine Q ms2) (spine c ms1)).
Proof.
  move e:(U)=>u cn. 
  elim: cn Γ A Cs I Q ms1 ms2 c s t1 t2 l1 l2 e=>{u}; 
  simpl; intros; subst; try discriminate.
  { rewrite spine_subst; simpl.
    rewrite H1.
    rewrite drespine_spine_Ind.
    rewrite spine_subst in H0; simpl in H0.
    rewrite spine_subst in H3; simpl in H3.
    rewrite spine_subst in H4; simpl in H4.
    rewrite H1 in H0.
    rewrite H1 in H3.
    rewrite H1 in H4.
    apply: typing_spine_Ind_Q2; eauto. }
  { rewrite H4 in H3. 
    inv H3; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H12; firstorder.
      move: (merge_re_re H15)=>[e1 e2].
      move: (u_Arrow_inv H13); firstorder.
      move: (u_Arrow_inv H6); firstorder.
      move: (s_Ind_inv H8); firstorder.
      have a : arity U A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
      { asimpl. rewrite H4; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H4. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- 
        (arity2 s (Ind A0 Cs U) A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity2_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H4. apply: typing_spine_strengthen; eauto. }
      have h13 : pure (A1 +u re Γ).
      { constructor. apply: re_pure. }
      have h14 : [ A1 +u re Γ |- c.[ren (+1)] :- 
        (Arrow A.[I] B.[up I] U).[ren (+1)] ].
      { apply: eweakeningU; eauto. }
      asimpl in h14.
      have h15 : [ A1 +u re Γ |- ids 0 :- A.[I].[ren (+1)] ].
      { apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        apply: u_Var.
        constructor.
        apply: re_pure. }
      asimpl in h15.
      have h16 := merge_re_re_re (A1 +u Γ).
      have h17 := u_Arrow_App h13 h14 h15 h16.
      asimpl in h17.
      pose proof
      (@constr_drespine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B (App c.[ren (+1)] (ids 0)) x.+1 s x3 x4
        H0 a h1 h2 h3 h4 h17); firstorder.
      simpl in H29.
      rewrite<-e1 in H29.
      rewrite<-pure_re in H29; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H14. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite constr_drespine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { replace B.[hd .: I] with B.[up I].[hd/] by autosubst.
          apply: u_Arrow_App.
          2:{ apply: H7. }
          2:{ apply: s_Conv. 
              apply: conv_sub.
              apply: conv_sym; eauto.
              rewrite<-e1 in H21; eauto.
              eauto. }
          { eauto. }
          { rewrite e2. rewrite<-!e1.
            rewrite<-pure_re; eauto.
            apply: merge_pure; eauto. } }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Arrow_inv in H11; firstorder; discriminate. } }
  { rewrite H3 in H2. 
    inv H2; try solve[exfalso; solve_sub_spine].
    { apply sub_Arrow_inv in H11; firstorder.
      move: (merge_re_re H14)=>[e1 e2].
      move: (u_Arrow_inv H12); firstorder.
      move: (u_Arrow_inv H5); firstorder.
      move: (s_Ind_inv H7); firstorder.
      have a : arity U A0.[ren (+1)].
      { apply: arity_ren; eauto. }
      have h1 : up I x.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U.
      { asimpl. rewrite H3; asimpl; eauto. }
      have h2 : [ re (A1 +u Γ) |- up I x.+1 :- A0.[ren (+1)] ].
      { asimpl. rewrite H3. apply: eweakeningU; eauto. }
      have h3 : [re (A1 +u Γ) |- Q.[ren (+1)] :- 
        (arity2 s (Ind A0 Cs U) A0).[ren (+1)]].
      { asimpl. apply: eweakeningU; eauto. }
      erewrite arity2_subst in h3; eauto.
      have h4 : [re (A1 +u Γ) |- B.[up I] :- x3 @ x4 ].
      { simpl.
        apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        eauto. }
      have h5 : merge (re Γ1) (re Γ2) (re Γ).
      { rewrite e1 e2. apply: merge_re_re_re. }
      have h6 : [ re Γ2 |- hd :- A1 ].
      { rewrite e2. rewrite<-e1.
        rewrite<-pure_re; eauto. }
      have h7 : pure (re Γ2).
      { apply: re_pure. }
      have h8 : [ re Γ2 |- B.[hd .: I] :- x3 @ x4 ].
      { simpl in h4. rewrite<-e1 in h4.
        move: (substitutionU h4 h6 h7 h5); asimpl.
        rewrite<-e2; eauto. }
      have h9 : B.[up I].[hd/] <: B0.[hd/].
      { apply: sub_subst; eauto. }
      asimpl in h9.
      have h10 : [ A1 +u re Γ1 |- B0 :- x0 @ x1 ].
      { rewrite<-pure_re; eauto. }
      have h11 : [ re Γ2 |- B0.[hd/] :- x0 @ x1 ].
      { rewrite e2.
        move: (substitutionU h10 h6 h7 h5)=>//=. }
      have h12 : typing_spine Γ2 B.[hd .: I] tl (spine (I x) ms2).
      { rewrite H3. apply: typing_spine_strengthen; eauto. }
      have h13 : pure (A1 +u re Γ).
      { constructor. apply: re_pure. }
      have h14 : [ A1 +u re Γ |- c.[ren (+1)] :- 
        (Arrow A.[I] B.[up I] U).[ren (+1)] ].
      { apply: eweakeningU; eauto. }
      asimpl in h14.
      have h15 : [ A1 +u re Γ |- ids 0 :- A.[I].[ren (+1)] ].
      { apply: context_convU.
        apply: conv_sym; eauto.
        rewrite <-re_re; eauto.
        apply: u_Var.
        constructor.
        apply: re_pure. }
      asimpl in h15.
      have h16 := merge_re_re_re (A1 +u Γ).
      have h17 := u_Arrow_App h13 h14 h15 h16.
      asimpl in h17.
      pose proof
      (@constr_drespine (A1 +u Γ) (up I) Cs..[up (ren (+1))] A0.[ren (+1)]
        Q.[ren (+1)] B (App c.[ren (+1)] (ids 0)) x.+1 s x3 x4
        H0 a h1 h2 h3 h4 h17); firstorder.
      simpl in H28.
      rewrite<-e1 in H28.
      rewrite<-pure_re in H28; eauto.
      apply: typing_spine_u_Lolli_cons.
      4:{ apply: H13. }
      2:{ apply: conv_sub.
          apply: conv_Lolli; eauto. }
      { eauto. }
      { apply: u_Lolli_max; eauto. }
      { eauto. }
      { erewrite constr_drespine_subst; eauto.
        2:{ asimpl. apply: ren_Var_False; eauto. }
        asimpl.
        apply: H1; eauto.
        { replace B.[hd .: I] with B.[up I].[hd/] by autosubst.
          apply: u_Arrow_App.
          2:{ apply: H6. }
          2:{ apply: s_Conv. 
              apply: conv_sub.
              apply: conv_sym; eauto.
              rewrite<-e1 in H20; eauto.
              eauto. }
          { eauto. }
          { rewrite e2. rewrite<-!e1.
            rewrite<-pure_re; eauto.
            apply: merge_pure; eauto. } }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. }
        { rewrite e2; eauto. } } }
    { apply sub_Arrow_inv in H10; firstorder; discriminate. } }
Qed.