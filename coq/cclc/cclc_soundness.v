From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness cclc_eval
  clc_linearity cclc_ast cclc_dual cclc_typing cclc_weakening 
  cclc_substitution cclc_linearity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma congr0_sym p q : congr0 p q -> congr0 q p.
Proof.
  elim; move=>*; eauto using congr0.
Qed.

Lemma congr0_type Γ p q : 
  Γ ⊢ p -> congr0 p q -> Γ ⊢ q.
Proof with eauto using cclc_type, congr0.
  move=>ty. elim: ty q=>{Γ p}.
  move=>Γ m A s tym q cr. inv cr.
  move=>Γ1 Γ2 Γ p q mrg typ ihp tyq ihq q0 cr. inv cr.
  { econstructor.
    apply: merge_sym...
    all: eauto. }
  { inv tyq.
    have[G[mrg1 mrg2]]:=merge_splitL (merge_sym mrg) H1.
    econstructor. 
    exact: mrg2.
    econstructor.
    exact: (merge_sym mrg1).
    all: eauto. }
  { inv typ.
    have[G[mrg1 mrg2]]:=merge_splitR mrg H1.
    econstructor. 
    exact: mrg2.
    exact: H3.
    econstructor.
    exact: mrg1.
    all: eauto. }
  { inv typ.
    have[_[e1 e2]]:=merge_re_re mrg.
    have mrg': 
      Ch A.[ren (+1)] :L Ch B :L Γ1 ∘ _: _: Γ2 => 
      Ch A.[ren (+1)] :L Ch B :L Γ.
      repeat econstructor; eauto.
    econstructor.
    exact: H0.
    rewrite<-e1; eauto.
    rewrite<-e1; eauto.
    econstructor...
    replace q.[ren (+2)]%P 
      with q.[ren (+1)].[ren (+1)]%P.
    apply: weakeningN.
    apply: weakeningN...
    rewrite proc_subst_comp.
    by asimpl. }
  { econstructor... }
  { econstructor.
    apply: mrg.
    apply: ihp...
    apply: congr0_sym...
    apply: ihq...
    apply: congr0_sym... }
  move=>Γ p A B i d tyA tyB typ ihp q cr. inv cr.
  { inv typ. 
    inv H1; inv H5.
    { have[_[e1 e2]]:=merge_re_re H2.
      econstructor.
      apply: H2.
      econstructor...
      rewrite e1...
      rewrite e1...
      apply: strengthen.
      apply: strengthen.
      rewrite proc_subst_comp.
      by asimpl. }
    { have os:of_sort (_: Ch B :L Γ2) 1 (Some L).
        repeat econstructor.
      have:=linearity H4 os. 
      have->//:=iren_occurs q0 iren1. }
    { have os:of_sort (Ch A.[ren (+1)] :L _: Γ2) 0 (Some L).
        econstructor.
      have:=linearity H4 os.
      have->//:=iren_occurs q0 iren0. }
    { have os:of_sort (Ch A.[ren (+1)] :L Ch B :L Γ2) 0 (Some L).
        econstructor.
      have:=linearity H4 os.
      have->//:=iren_occurs q0 iren0. } }
  { econstructor; eauto. }
  { econstructor; eauto.
    apply: ihp; eauto.
    apply: congr0_sym... }
Qed.

Lemma congr_type Γ p q : 
  Γ ⊢ p -> p ≡ q -> Γ ⊢ q.
Proof.
  move=>ty e. elim: e Γ ty=>//={q}.
  move=>y z e ih cr Γ typ.
    apply: congr0_type.
    apply: ih; eauto.
    eauto.
  move=>y z e ih cr Γ typ.
    apply: congr0_type.
    apply: ih; eauto.
    apply: congr0_sym; eauto.
Qed.

Lemma congr_expr_inj m p : ⟨ m ⟩ ≡ p -> p = ⟨ m ⟩.
Proof.
  elim=>//={p}.
  move=>y z e1 e2 cr; subst. inv cr.
  move=>y z e1 e2 cr; subst. inv cr.
Qed.

Lemma step_expr_inj m p : 
  ⟨ m ⟩ --> p -> exists n, p = ⟨ n ⟩ /\ m ~> n.
Proof.
  move e:(⟨ m ⟩)=>n st. elim: st m e=>//={n p}.
  move=>m n st m0 [e]; subst.
    exists n; eauto.
  move=>p p' q q' e1 st ih e2 m e3; subst.
  move/congr_expr_inj in e1; subst.
  have[n[e st']]:=ih _ erefl; subst.
  move/congr_expr_inj in e2; subst.
  by exists n.
Qed.

Theorem subject_step Γ p q :
  ok Γ -> Γ ⊢ p -> p --> q -> Γ ⊢ q.
Proof.
  move=>wf ty st. elim: st Γ ty wf=>{p q}.
  move=>c d v val Γ ty wf.
  { inv ty. inv H4. inv H5; inv H6.
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      inv H8.
      have {}wf2:ok (_: _: Γ2).
        repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf2 H4.
      inv mrg. inv H8.
      have os:of_sort (_: _: Γ4) 1 None.
        repeat constructor.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[e0[e1 e2]]:=merge_re_re H5.
      inv H7. inv H8.
      have{H1}//=tyA:=clc_weakening.weakeningN H1.
      have wf1':ok (Ch A.[ren (+1)] :L _: Γ1).
        econstructor.
        constructor; eauto.
        simpl; rewrite e1; eauto.
      have wf2':ok (_: Ch B :L Γ2).
        constructor.
        econstructor; eauto.
        rewrite e2; eauto.
      have{wf1' H4}[G1[G2[B0[t1[mrg1[ty1 h1]]]]]]:=plug_inv wf1' H4.
      inv mrg1. inv H4.
      have /h1{}h1:~Ch A.[ren (+1)] :L _: Γ4 |> U.
      move=>k. inv k.
      have{wf2' H6}[G3[G4[B1[t2[mrg2[ty2 h2]]]]]]:=plug_inv wf2' H6.
      inv mrg2. inv H4.
      have /h2{}h2 :~_: Ch B :L Γ6 |> U.
      move=>k. inv k. inv H1.
      have wf3:ok (Ch A.[ren (+1)] :L _: Γ4).
      have[_[e3 e4]]:=merge_re_re H7.
      econstructor; simpl.
      econstructor.
      have[]//:=merge_context_ok_inv H7 wf1.
      rewrite e3 e1; eauto.
      have//=[l tyB0]:=validity wf3 ty1.
      have[_[e3 e4]]:=merge_re_re H6.
      have[_[e5 e6]]:=merge_re_re H7.
      have{ty1}[G1[G2[A2[B2[s1[t[k[sb[mrg[tyS tyv]]]]]]]]]]:=app_inv ty1.
      have{tyS}[A3[B3[s2[e7[sb1 tyv0]]]]]:=send_inv tyS; subst.
      have[wf4 wf5]:=merge_context_ok_inv H6 wf2.
      have wf6: ok (Ch B :L Γ6).
      econstructor; eauto. rewrite e3 e2; eauto.
      have[_[B'[_ eB1]]]:=narity_ren1 wf6 ty2; subst.
      have ty3:_: Ch B :L Γ6 ⊢ (Recv (Var 0)).[ren (+1)] : B'.[ren (+1)] : t2 by asimpl.
      move/clc_substitution.strengthen in ty3.
      have//={ty3}[l0 tyB']:=validity wf6 ty3.
      have{ty2}[A4[B4[s3[e7[sb2 tyv1]]]]]:=recv_inv ty2; subst.
      have[_[A'[_ eA']]]:=narity_ren1 wf6 tyv1.
      destruct A'; inv eA'.
      destruct A'; inv H1.
      pose proof (sub_subst (ren (subn^~ 1)) sb2).
      asimpl in H.
      have er: (+1) >>> subn_rec^~ 1 = id.
      f_ext. move=>[|x]; asimpl=>//.
      move: er H=>{sb2}->; asimpl=>sb2.
      inv mrg.
      { have{tyv0}[A5[t2[hs0[sb3 e]]]]:=var_inv tyv0; subst.
        have tyv':_: Ch B :L Γ6 ⊢ (Var 0).[ren (+1)] : (Ch (Inp A' B1 s4)).[ren (+1)] : L.
        simpl; eauto.
        have{}tyv':=clc_substitution.strengthen tyv'.
        have//=[l1 tyC]:=validity wf6 tyv'.
        have{tyC l1}[i0 tyI]:=ch_inv tyC.
        have{tyI i0}[l1[tyA'[_ tyB1]]]:=inp_inv tyI.
        have{tyv1}[A6[t3[hs1[sb4 e]]]]:=var_inv tyv1; subst.
        inv hs0. inv hs1. inv H8.
        asimpl in sb3. asimpl in sb4.
        have{}sb3:=sub_ch_inv sb3.
        have{}sb4:=sub_ch_inv sb4.
        have{sb1}[eA0[sb5[e7[e8 _]]]]:=sub_pi_inv sb1; subst.
        inv H0; asimpl in sb3; asimpl in sb4.
        move=>{sb5}; exfalso; solve_sub.
        move=>{sb5}; exfalso; solve_sub.
        move=>{sb5}; exfalso; solve_sub.
        have{sb3}[eA1[sb6 e7]]:=sub_out_inv sb3; subst.
        have{sb4}[eA2[sb7 e8]]:=sub_inp_inv sb4; subst.
        have {eA0 eA1 eA2}eA:A2 === A'.[ren (+1)].
        apply: conv_trans. apply: (conv_sym eA0).
        apply: conv_trans. apply: (conv_sym eA1).
        apply: eA2.
        have{sb6}sb5:=sub_trans (sub_ch sb6) sb5.
        have{}sb7:=sub_ch sb7.
        pose proof (sub_trans (sub_subst (v .: ids) sb5) sb)=>{sb5}.
        pose proof (sub_subst (v .: ids) sb7)=>{sb7}.
        asimpl in H0. asimpl in H8. inv H4.
        have[wf7 wf8]:=merge_context_ok_inv H7 wf1.
        have[wf9 wf10]:=merge_context_ok_inv H12 wf7.
        have wf11:ok (_: Γ9). repeat constructor; eauto.
        have[vx[Ax[evx eAx]]]:=narity_ren1 wf11 tyv; subst.
        move/clc_substitution.strengthen in tyv.
        have[vy[Ay[evy eAy]]]:=narity_ren1 wf10 tyv; subst.
        move/clc_substitution.strengthen in tyv.
        replace (Ch B4.[vy.[ren (+1)].[ren (+1)] .: ren (+2)])
          with (Ch B4.[vy/].[ren (+1)].[ren (+1)]) in H0 by autosubst.
        replace (Ch B5.[vy.[ren (+1)].[ren (+1)] .: ren (+2)])
          with (Ch B5.[vy/].[ren (+1)].[ren (+1)]) in H8 by autosubst.
        replace (Ch B1.[vy.[ren (+1)].[ren (+1)] .: ren (+1)])
          with (Ch B1.[vy.[ren (+1)]/]).[ren (+1)] in H8 by autosubst.
        pose proof (sub_subst (ren (subn^~ 1)) H8). asimpl in H4.
        have er: (+2) >>> subn_rec^~ 1 = (+1).
        f_ext. move=>[|x]//.
        rewrite er in H4.
        have {}er: (+1) >>> subn_rec^~ 1 = id.
        f_ext. move=>[|x]//.
        rewrite er in H4; asimpl in H4=>{er}.
        replace (Ch B5.[vy.[ren (+1)] .: ren (+1)])
          with (Ch B5.[vy/].[ren (+1)]) in H4 by autosubst.
        have[G[mrg1 mrg2]]:=merge_splitL H7 H12. inv H1.
        have[_[e7 e8]]:=merge_re_re H12.
        have mrg:
          Ch B4.[vy/].[ren (+1)] :L _: Γ8 ∘ _: _: Γ5 =>
          Ch B4.[vy/].[ren (+1)] :L _: G.
        repeat econstructor; eauto.
        have {mrg}h1:=h1 _ _ _ mrg.
        have /h1{}h1: Ch B4.[vy/].[ren (+1)] :L _: Γ8 ⊢ Var 0 : B0 : L.
        apply: clc_conv; simpl. apply: H0.
        econstructor.
        repeat econstructor; eauto.
        rewrite e7; eauto.
        have[G1[G2[mrg3[mrg4 mrg5]]]]:=merge_distr H5 mrg2 H6.
        apply merge_pureR in mrg4; eauto; subst.
        have mrg:
          _: Ch B5.[vy/] :L Γ9 ∘ _: _: Γ7 => _: Ch B5.[vy/] :L G2.
        repeat constructor; eauto.
        have {mrg}h2:=h2 _ _ _ mrg.
        have /h2{}h2:
          _: Ch B5.[vy/] :L Γ9 ⊢ Pair vy.[ren (+1)].[ren (+1)]%subst (Var 1) L : B'.[ren (+1)] : L.
        replace (Pair vy.[ren (+1)].[ren (+1)]%subst (Var 1) L)
          with (Pair vy.[ren (+1)] (Var 0) L).[ren (+1)]%subst by autosubst.
        apply: clc_weakening.weakeningN.
        have[Ax eAx]:=narity_ren0 tyA'; subst.
        apply: clc_conv; simpl. apply: sb2. inv k.
        have k: Ch B5.[vy/] :L [Γ9] |> L by apply key_impure.
        have //=wtyA':=clc_weakening.weakeningN tyA'.
        have tyvA': _: _: Γ9 ⊢ vy.[ren (+1)].[ren (+1)] : Ax.[ren (+1)].[ren (+1)] : s4.
        apply: clc_conv; simpl. apply: conv_sub. apply: eA.
        apply: clc_weakening.weakeningN. apply: clc_weakening.weakeningN. eauto.
        rewrite e8 e5 e0. rewrite<-e3. eauto.
        have tyvAx:=clc_substitution.strengthen tyvA'.
        move/clc_substitution.strengthen in tyvA'.
        move/clc_substitution.strengthen in tyvA'.
        replace (s4 @ l1) with (s4 @ l1).[ren (+1)].[ren (+1)] in wtyA' by autosubst.
        move/clc_substitution.strengthen in wtyA'.
        move/clc_substitution.strengthen in wtyA'.
        econstructor; simpl. apply: H9. apply: k.
        econstructor. apply: merge_reR.
        asimpl.
        rewrite e8 e5 e0. rewrite<-e3.
        econstructor; simpl; eauto.
        destruct s4; simpl; constructor.
        constructor. apply: re_pure.
        rewrite<-re_invo.
        econstructor; eauto.
        destruct s4; repeat constructor; eauto using re_pure.
        apply: clc_weakening.weakeningN; eauto.
        have tyCh:_: [Γ6] ⊢ Ch B1.[vy.[ren (+1)]/] : L @ l1 : U.
        destruct s4.
        have mrg:_: [Γ6] ∘ _: Γ9 => _: [Γ6].
        constructor. inv H9. replace Γ9 with [Γ9].
        rewrite e8 e5 e0. rewrite<-e3. apply: merge_re_id.
        by rewrite<-pure_re.
        have //=tysB1:=clc_substitution.substitution tyB1 H9 mrg tyvAx.
        econstructor; eauto.
        constructor. apply: re_pure.
        have //=tysB1:=clc_substitution.substitutionN tyB1 tyvAx.
        econstructor; eauto.
        constructor. apply: re_pure.
        apply: clc_conv; simpl.
        apply: H4.
        econstructor.
        econstructor.
        apply: re_pure.
        rewrite<-re_invo.
        rewrite e8 e5 e0. rewrite<-e3; eauto.
        rewrite e8 e5 e0. rewrite<-e3; eauto.

        have dv:B4.[vy/] ~ B5.[vy/].
        apply: dual_subst; eauto.
        replace (L @ i) with (L @ i).[ren (+1)] in tyA by autosubst.
        replace (Ch (Out A4 B4 s4).[ren (+1)])
          with (Ch (Out A4 B4 s4)).[ren (+1)] in tyA by autosubst.
        apply clc_substitution.strengthen in tyA.
        have[Ax eAx]:=narity_ren0 tyA'; subst.
        have er: (+2) >>> subn_rec^~ 1 = (+1).
        f_ext. move=>[|x]//.
        pose proof (conv_subst (ren (subn^~ 1)) eA).
        asimpl in H1. rewrite er in H1.
        have {}er: (+1) >>> subn_rec^~ 1 = id.
        f_ext. move=>[|x]//.
        pose proof (conv_subst (ren (subn^~ 1)) H1).
        asimpl in H9. rewrite er in H9. asimpl in H9.
        have[Az[t[hs[sbz e]]]]:=var_inv tyv'; subst.
        inv hs. asimpl in sbz.
        move/sub_ch_inv in sbz.
        have[eAx _]:=sub_inp_inv sbz.
        pose proof (conv_subst (ren (subn^~ 1)) eAx).
        asimpl in H11. rewrite er in H11. asimpl in H11.
        inv k. inv H15.
        have[i1 tyI]:=ch_inv H2.
        have[i2 tyO]:=ch_inv tyA.
        have{i1 tyI}[i1[tyA4[_ tyB5]]]:=inp_inv tyI.
        have{i2 tyO}[i2[tyA5[_ tyB6]]]:=out_inv tyO.
        have {}tyv:Γ9 ⊢ vy : A4 : s4.
        { apply: clc_conv.
          apply: conv_sub.
          apply: conv_trans.
          apply: H9.
          apply: (conv_sym H11).
          eauto.
          rewrite e8 e5 e1; eauto. }
        have tyC4: [Γ] ⊢ Ch B4.[vy/] : L @ (maxn i1 i2) : U.
        { apply: clc_conv.
          apply: sub_sort.
          apply: leq_maxr.
          destruct s4.
          have mrg:[Γ] ∘ Γ9 => [Γ].
          replace Γ9 with [Γ9].
          rewrite e8 e5 e1. apply: merge_re_id.
          rewrite<-pure_re; eauto.
          have//=tyB4:=clc_substitution.substitution tyB6 H16 mrg tyv.
          econstructor; eauto. apply: re_pure.
          have//=tyB4:=clc_substitution.substitutionN tyB6 tyv.
          econstructor; eauto. apply: re_pure.
          constructor. apply: re_pure. }
        have tyC5: [Γ] ⊢ Ch B5.[vy/] : L @ (maxn i1 i2) : U.
        { apply: clc_conv.
          apply: sub_sort.
          apply: leq_maxl.
          destruct s4.
          have mrg:[Γ] ∘ Γ9 => [Γ].
          replace Γ9 with [Γ9].
          rewrite e8 e5 e1. apply: merge_re_id.
          rewrite<-pure_re; eauto.
          have//=tyB4:=clc_substitution.substitution tyB5 H16 mrg tyv.
          econstructor; eauto. apply: re_pure.
          have//=tyB4:=clc_substitution.substitutionN tyB5 tyv.
          econstructor; eauto. apply: re_pure.
          constructor. apply: re_pure. }
        econstructor.
        apply: dv.
        apply: tyC4.
        apply: tyC5.
        have mrg:
          Ch B4.[vy/].[ren (+1)] :L _: G ∘ _: Ch B5.[vy/] :L G2 =>
          Ch B4.[vy/].[ren (+1)] :L Ch B5.[vy/] :L Γ.
        repeat econstructor; eauto.
        econstructor.
        apply: mrg.
        econstructor; eauto.
        econstructor; eauto. }
      have os:of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity tyv0 os.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//:=clc_linearity.narity ty2 os. inv H4.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity ty1 os. }
      have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[_[e1 e2]]:=merge_re_re H5.
      inv H7.
      have {}wf1:ok (_: Ch B :L Γ1).
        constructor.
        econstructor; eauto.
        rewrite e1; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H4.
      inv mrg.
      have os:of_sort (_: Γ0) 0 None by constructor.
      have//=oc:=clc_linearity.narity ty os.
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      inv H7.
      have {}wf1:ok (_: _: Γ1).
        repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H4.
      inv mrg.
      have os:of_sort (_: Γ0) 0 None.
        repeat constructor.
      have//=oc:=clc_linearity.narity ty os. } }
  move=>c d v val Γ ty wf. admit.
  move=>c d Γ ty wf. admit.
  move=>c d Γ ty wf. admit.
  move=>m n st Γ ty wf. inv ty.
    econstructor.
    apply: subject_step; eauto.
  move=>o p q st ih Γ ty wf. inv ty.
    have[wf1 wf2]:=merge_context_ok_inv H1 wf.
    econstructor; eauto.
  move=>p q st ih Γ ty wf. inv ty.
    econstructor; eauto.
    have tyA:=clc_weakening.weakeningN H1.
    apply: ih; eauto.
    econstructor.
    econstructor; eauto.
    asimpl in tyA; eauto.
  move=>p p' q q' e1 st ih e2 Γ typ wf.
    have typ':=congr_type typ e1.
    have tyq':=ih _ typ' wf.
    have//:=congr_type tyq' e2.
Qed.
