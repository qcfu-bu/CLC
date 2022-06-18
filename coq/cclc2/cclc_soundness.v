From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_act cclc_eval
  clc_linearity cclc_ast cclc_typing cclc_weakening
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
      Ch (~~r2) A.[ren (+1)] :L Ch r2 A :L Γ1 ∘ _: _: Γ2 =>
      Ch (~~r2) A.[ren (+1)] :L Ch r2 A :L Γ.
      repeat econstructor; eauto.
    econstructor; eauto.
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
  move=>Γ p r1 r2 A d tyA typ ihp q cr. inv cr.
  { inv typ. 
    inv H1; inv H5.
    { have[_[e1 e2]]:=merge_re_re H2.
      econstructor.
      apply: H2.
      econstructor...
      rewrite e1...
      apply: strengthen.
      apply: strengthen.
      rewrite proc_subst_comp.
      by asimpl. }
    { have os:of_sort (_: Ch r2 A :L Γ2) 1 (Some L).
        repeat econstructor.
      have:=linearity H4 os. 
      have->//:=iren_occurs q0 iren1. }
    { have os:of_sort (Ch (~~r2) A.[ren (+1)] :L _: Γ2) 0 (Some L).
        econstructor.
      have:=linearity H4 os.
      have->//:=iren_occurs q0 iren0. }
    { have os:of_sort (Ch (~~r2) A.[ren (+1)] :L Ch r2 A :L Γ2) 0 (Some L).
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

Theorem subject_step Γ p q :
  ok Γ -> Γ ⊢ p -> p --> q -> Γ ⊢ q.
Proof.
  move=>wf ty st. elim: st Γ ty wf=>{p q}.
  move=>c c' m m' e1 e2 Γ ty wf; subst.
  { inv ty.
    have{}H1:=clc_weakening.weakeningN H1.
    have{}H1:=clc_weakening.weakeningN H1.
    asimpl in H1.
    rewrite<-eren_comp in H1.
    have{H1}[G1[G2[B[t[mrg[tyF h]]]]]]:=plug_inv (n_ok (n_ok wf)) H1.
    inv mrg. inv H2.
    have[wf0 wf3]:=merge_context_ok_inv H3 wf.
    have[_[B'[_ e]]]:=narity_ren1 (n_ok wf0) tyF; subst.
    replace (Fork (Var 0) m).[ren (+2)]
      with (Fork (Var 0) m).[ren (+1)].[ren (+1)] in tyF by autosubst.
    have {}tyF:=clc_substitution.strengthen tyF.
    have[_[B[_ e]]]:=narity_ren1 wf0 tyF; subst.
    have {}tyF:=clc_substitution.strengthen tyF.
    have[G1[G2[r1[r2[A0[B0[s0[t0[e[sb0[mrg[d[tyA[tyv tym]]]]]]]]]]]]]]:=
      fork_inv tyF; subst.
    have[A1[s1[hs[sb1 e]]]]:=var_inv tyv; subst.
    inv hs.
    have/h{}h:~_: _: Γ0 |> U.
    { move=>k. inv k. inv H1.
      have[k1 k2]:=merge_pure_inv mrg H2.
      inv k1. }
    inv mrg. inv H3.
    simpl in tyA.
    have//=tyB':=validity wf0 tyF.
    inv wf. inv wf0.
    have[wf1 wf4]:=merge_context_ok_inv H5 H3.
    have[wf5 wf2]:=merge_context_ok_inv H6 H2.
    have[A'[_[eA _]]]:=narity_ren1 (re_ok wf5) tyA; subst.
    have[G[mrg1 mrg2]]:=merge_splitL H6 H5.
    have/h{}h:
      Ch (~~r2) A'.[ren (+2)] :L _: A2 :L Γ1 ∘ _: _: _: Γ2 =>
      Ch (~~r2) A'.[ren (+2)] :L _: A2 :L G.
    { repeat constructor; eauto. }
    asimpl in h.
    have/h{}h: Ch (~~r2) A'.[ren (+2)] :L _: A2 :L Γ1 ⊢ Pair (Var 0) (Var 2) L : B.[ren (+2)] : L.
    { pose proof (conv_subst (ren (+2)) sb0).
      have[_[e1 e4]]:=merge_re_re H5.
      asimpl in H0.
      have mrg:
        Ch (~~r2) A'.[ren (+2)] :L _: _: [Γ1] ∘ _: _: A2 :L Γ1 =>
        Ch (~~r2) A'.[ren (+2)] :L _: A2 :L Γ1.
      { repeat constructor.
        apply: merge_reL. }
      apply: clc_conv; simpl.
      apply: H0.
      econstructor; simpl.
      apply: key_impure.
      apply: key_impure.
      apply: mrg.
      asimpl.
      econstructor; simpl.
      constructor.
      repeat constructor. apply: re_pure.
      have{}tyA:=clc_weakening.weakeningN tyA.
      have{}tyA:=clc_weakening.weakeningN tyA.
      asimpl in tyA; eauto.
      repeat constructor. apply: re_pure.
      rewrite e1; eauto.
      repeat constructor. apply: re_pure.
      constructor.
      replace (Ch (~~r2) A'.[ren (+2)]) with (Ch (~~r2) A').[ren (+2)] by autosubst.
      replace (Ch (~~r2) A'.[ren (+3)]) with (Ch (~~r2) A').[ren (+2)].[ren (+1)] by autosubst.
      repeat constructor. apply: re_pure.
      have{}tyv:=clc_weakening.weakeningN tyv.
      have{}tyv:=clc_weakening.weakeningN tyv.
      asimpl in tyv; eauto.
      have{}tyB':=clc_weakening.weakeningN tyB'.
      have{}tyB':=clc_weakening.weakeningN tyB'.
      asimpl in tyB'. rewrite e1; eauto. }
    have{}tym:=clc_weakening.weakeningN tym.
    have{}tym:=clc_weakening.weakeningN tym.
    asimpl in tym.
    have tyv1:_: Ch r2 A'.[ren (+1)] :L _: [Γ4] ⊢ Var 1 : Ch r2 A'.[ren (+3)] : L.
    { replace (Var 1) with (Var 0).[ren (+1)] by autosubst.
      replace (Ch r2 A'.[ren (+3)])
        with (Ch r2 A').[ren (+1)].[ren (+1)].[ren (+1)] by autosubst.
      apply: clc_weakening.weakeningN.
      constructor.
      repeat constructor. apply: re_pure. }
    have mrg:
      _: _: _: Γ4 ∘ _: Ch r2 A'.[ren (+1)] :L _: [Γ4] =>
      _: Ch r2 A'.[ren (+1)] :L _: Γ4.
    { repeat constructor. apply: merge_reR. }
    have k: _: Ch r2 A'.[ren (+1)] :L _: [Γ4] |> L by apply key_impure.
    have tyApp:=clc_app k mrg tym tyv1. asimpl in tyApp.
    have[_[e1 e4]]:=merge_re_re H5.
    have[_[e5 e2]]:=merge_re_re H6.
    econstructor; simpl.
    apply: (erefl (~~r2)).
    rewrite<-e5; eauto.
    asimpl.
    have {}mrg:
      Ch (~~r2) A'.[ren (+2)] :L _: A2 :L G ∘ _: Ch r2 A'.[ren (+1)] :L _: Γ4 =>
      Ch (~~r2) A'.[ren (+2)] :L Ch r2 A'.[ren (+1)] :L A2 :L Γ6.
    { repeat constructor; eauto. }
    econstructor.
    apply: mrg.
    econstructor. apply: h.
    econstructor. apply: tyApp. }
  move=>c d v Γ ty wf.
  { inv ty. inv H3. inv H2; inv H4.
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      inv H6.
      have {}wf2:ok (_: _: Γ2).
      repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf2 H2.
      inv mrg. inv H6.
      have os:of_sort (_: _: Γ4) 1 None.
      repeat constructor.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      have[e0[e1 e2]]:=merge_re_re H3.
      inv H5. inv H6.
      have{}H1:=clc_weakening.weakeningN H1.
      have wf1' : ok (Ch (~~r2) A.[ren (+1)] :L _: Γ1).
      { econstructor=>//=.
        constructor; eauto.
        rewrite e1.
        replace (Sort L) with (Sort L).[ren (+1)] by autosubst.
        replace (Ch (~~r2) A.[ren (+1)])
          with (Ch (~~r2) A).[ren (+1)] by autosubst.
        apply: clc_weakening.eweakeningN; eauto.
        constructor.
        apply: re_pure.
        apply: clc_substitution.strengthen; eauto. }
      have wf2' : ok (_: Ch r2 A :L Γ2).
      { repeat constructor; eauto.
        apply: re_pure.
        rewrite e2.
        apply: clc_substitution.strengthen; eauto. }
      have{wf1' H2}[G1[G2[B0[t1[mrg1[ty1 h1]]]]]]:=plug_inv wf1' H2.
      inv mrg1. inv H5.
      have /h1{}h1:~Ch (~~r2) A.[ren (+1)] :L _: Γ4 |> U.
      { move=>k. inv k. }
      have{wf2' H4}[G3[G4[B1[t2[mrg2[ty2 h2]]]]]]:=plug_inv wf2' H4.
      inv mrg2. inv H4.
      have/h2{}h2:~_: Ch r2 A :L Γ6 |> U.
      { move=>k. inv k. inv H0. }
      have wf3 : ok (Ch (~~r2) A.[ren (+1)] :L _: Γ4).
      { have[_[e3 e4]]:=merge_re_re H6.
        econstructor; simpl.
        constructor.
        have[]//:=merge_context_ok_inv H6 wf1.
        repeat constructor.
        apply: re_pure.
        rewrite e3 e1; eauto. }
      have//=tyB0:=validity wf3 ty1.
      have[_[e3 e4]]:=merge_re_re H5.
      have[_[e5 e6]]:=merge_re_re H6.
      have[G1[G2[A2[B2[s1[t[k[sb[mrg[tyS tyv]]]]]]]]]]:=app_inv ty1.
      have[r3[r4[A3[B3[s2[e7[sb1[xor1 tyv0]]]]]]]]:=send_inv tyS; subst.
      have[wf4 wf5]:=merge_context_ok_inv H5 wf2.
      have wf6 : ok (Ch r2 A :L Γ6).
      { repeat constructor; eauto.
        apply: re_pure.
        rewrite e3 e2.
        apply: clc_substitution.strengthen; eauto. }
      have[_[B'[_ eB1]]]:=narity_ren1 wf6 ty2; subst.
      have ty3 : _: Ch r2 A :L Γ6 ⊢ (Recv (Var 0)).[ren (+1)] : B'.[ren (+1)] : t2 by asimpl.
      move/clc_substitution.strengthen in ty3.
      have//={ty3}tyB':=validity wf6 ty3.
      have[r5[r6[A4[B4[s3[e7[sb2[xor2 tyv1]]]]]]]]:=recv_inv ty2; subst.
      have[_[A'[_ eA']]]:=narity_ren1 wf6 tyv1.
      destruct A'; inv eA'.
      destruct A'; inv H2.
      pose proof (conv_subst (ren (subn^~ 1)) sb2).
      asimpl in H.
      have er: (+1) >>> subn_rec^~ 1 = id.
      f_ext. move=>[|x]; asimpl=>//.
      move: er H=>{sb2}->; asimpl=>sb2.
      inv mrg.
      { have{tyv0}[A5[t2[hs0[sb3 e]]]]:=var_inv tyv0; subst.
        have tyv' : _: Ch r2 A :L Γ6 ⊢ (Var 0).[ren (+1)] : (Ch r (Act r0 A' B s4)).[ren (+1)] : L.
        simpl; eauto.
        have{}tyv':=clc_substitution.strengthen tyv'.
        have//=tyC:=validity wf6 tyv'.
        have{tyC} tyI:=ch_inv tyC.
        have{tyI}[tyA'[_ tyB1]]:=act_inv tyI.
        have{tyv1}[A6[t3[hs1[sb4 e]]]]:=var_inv tyv1; subst.
        inv hs0. inv hs1. inv H7.
        asimpl in sb3. asimpl in sb4.
        have{sb3}[e7 sb3]:=ch_inj sb3; subst.
        have{sb4}[e7 sb4]:=ch_inj sb4; subst.
        have[eA0[sb5[e7[e8 _]]]]:=pi_inj sb1; subst.
        have tyA:=clc_substitution.strengthen H1.
        have[A6[B6[ty6[sb6i sb6]]]]:=dual_conv (re_ok wf) sb3 tyA can_cancel2. asimpl in sb6.
        have[A7[B7[ty7[sb7i sb7]]]]:=dual_conv (re_ok wf) sb4 tyA can_cancel2. asimpl in sb7.
        have sb8:Act r4 A3 B3 s1 === Act r0 A'.[ren (+1)] B.[ren (0 .: (+2))] s4.
        { apply: conv_trans.
          apply: conv_sym.
          apply: sb3.
          eauto. }
        have[eA[eB[e7 e8]]]:=act_inj sb8; subst.
        have[eA7[eB7 _]]:=act_inj sb7; subst.
        have[eA6[eB6 _]]:=act_inj sb6; subst.
        have{}eB6:=conv_ch (~~r) eB6.
        have{}eB7:=conv_ch r eB7.
        have{}eB6:Ch (~~ r) B6.[ren (0 .: (+3))] === B2.
        { apply: conv_trans.
          apply: eB6.
          apply: sb5. }
        pose proof (conv_subst (v .: ids) eB6). asimpl in H.
        pose proof (conv_subst (v .: ids) eB7). asimpl in H7.
        have{}eA:=conv_trans _ (conv_sym eA0) eA.
        pose proof (conv_trans _ H sb).
        have[wf7 wf8]:=merge_context_ok_inv H6 wf1.
        inv H4.
        have[wf9 wf10]:=merge_context_ok_inv H12 wf7.
        have wf11 : ok (_: Γ9). repeat constructor; eauto.
        have[vx[Ax[evx eAx]]]:=narity_ren1 wf11 tyv; subst.
        move/clc_substitution.strengthen in tyv.
        have[vy[Ay[evy eAy]]]:=narity_ren1 wf10 tyv; subst.
        move/clc_substitution.strengthen in tyv.
        replace (Ch (~~r) B6.[vy.[ren (+1)].[ren (+1)] .: ren (+2)])
          with (Ch (~~r) B6.[vy/].[ren (+1)].[ren (+1)]) in H8 by autosubst.
        replace (Ch r B7.[vy.[ren (+1)].[ren (+1)] .: ren (+2)])
          with (Ch r B7.[vy/].[ren (+1)].[ren (+1)]) in H7 by autosubst.
        replace (Ch r B.[vy.[ren (+1)].[ren (+1)] .: ren (+1)])
          with (Ch r B.[vy.[ren (+1)]/]).[ren (+1)] in H7 by autosubst.
        pose proof (conv_subst (ren (subn^~ 1)) H7). asimpl in H4.
        have er: (+2) >>> subn_rec^~ 1 = (+1).
        f_ext. move=>[|x]//.
        rewrite er in H4.
        have {}er: (+1) >>> subn_rec^~ 1 = id.
        f_ext. move=>[|x]//.
        rewrite er in H4; asimpl in H4=>{er}.
        replace (Ch r B7.[vy.[ren (+1)] .: ren (+1)])
          with (Ch r B7.[vy/].[ren (+1)]) in H4 by autosubst.
        have[G[mrg1 mrg2]]:=merge_splitL H6 H12. inv H0.
        have[_[e7 e8]]:=merge_re_re H12.
        have mrg:
          Ch (~~r) B6.[vy/].[ren (+1)] :L _: Γ8 ∘ _: _: Γ5 =>
          Ch (~~r) B6.[vy/].[ren (+1)] :L _: G.
        repeat econstructor; eauto.
        have{mrg}h1:=h1 _ _ _ mrg.
        have /h1{}h1: Ch (~~r) B6.[vy/].[ren (+1)] :L _: Γ8 ⊢ Var 0 : B0 : L.
        { apply: clc_conv; simpl. apply: H8.
          econstructor.
          repeat constructor; eauto.
          rewrite e7; eauto. }
        have[G1[G2[mrg3[mrg4 mrg5]]]]:=merge_distr H3 mrg2 H5.
        apply merge_pureR in mrg4; eauto; subst.
        have mrg:
          _: Ch r B7.[vy/] :L Γ9 ∘ _: _: Γ7 => _: Ch r B7.[vy/] :L G2.
        repeat constructor; eauto.
        have {mrg}h2:=h2 _ _ _ mrg.
        have /h2{}h2:
          _: Ch r B7.[vy/] :L Γ9 ⊢ Pair vy.[ren (+1)].[ren (+1)]%subst (Var 1) L : B'.[ren (+1)] : L.
        { replace (Pair vy.[ren (+1)].[ren (+1)]%subst (Var 1) L)
            with (Pair vy.[ren (+1)] (Var 0) L).[ren (+1)]%subst by autosubst.
          apply: clc_weakening.weakeningN.
          have[Ax eAx]:=narity_ren0 tyA'; subst.
          apply: clc_conv; simpl. apply: sb2. inv k.
          have k: Ch r B7.[vy/] :L [Γ9] |> L by apply key_impure.
          have //=wtyA':=clc_weakening.weakeningN tyA'.
          have tyvA': _: _: Γ9 ⊢ vy.[ren (+1)].[ren (+1)] : Ax.[ren (+1)].[ren (+1)] : s4.
          apply: clc_conv; simpl. apply: eA.
          apply: clc_weakening.weakeningN. apply: clc_weakening.weakeningN. eauto.
          rewrite e8 e5 e0. rewrite<-e3. eauto.
          have tyvAx:=clc_substitution.strengthen tyvA'.
          move/clc_substitution.strengthen in tyvA'.
          move/clc_substitution.strengthen in tyvA'.
          replace (Sort s4) with (Sort s4).[ren (+1)].[ren (+1)] in wtyA' by autosubst.
          move/clc_substitution.strengthen in wtyA'.
          move/clc_substitution.strengthen in wtyA'.
          econstructor; simpl. apply: H9. apply: k.
          econstructor. apply: merge_reR.
          rewrite e8 e5 e0. rewrite<-e3.
          econstructor; simpl; eauto.
          destruct s4; simpl; constructor.
          constructor. apply: re_pure.
          rewrite<-re_invo.
          econstructor; eauto.
          destruct s4; repeat constructor; eauto using re_pure.
          simpl in tyB1. rewrite<-re_invo in tyB1; eauto.
          apply: clc_weakening.weakeningN; eauto.
          have tyCh:_: [Γ6] ⊢ Ch r B.[vy.[ren (+1)]/] : Sort L : U.
          destruct s4.
          have mrg:_: [Γ6] ∘ _: Γ9 => _: [Γ6].
          constructor. inv H9. replace Γ9 with [Γ9].
          rewrite e8 e5 e0. rewrite<-e3. apply: merge_re_id.
          by rewrite<-pure_re.
          simpl in tyB1. rewrite<-re_invo in tyB1.
          have //=tysB1:=clc_substitution.substitution tyB1 H9 mrg tyvAx.
          econstructor; eauto.
          constructor. apply: re_pure.
          simpl in tyB1. rewrite<-re_invo in tyB1.
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
          rewrite e8 e5 e0. rewrite<-e3; eauto. }
        have[Ax eAx]:=narity_ren0 tyA'; subst.
        have er: (+2) >>> subn_rec^~ 1 = (+1).
        f_ext. move=>[|x]//.
        pose proof (conv_subst (ren (subn^~ 1)) sb7i).
        asimpl in H0. rewrite er in H0.
        pose proof (conv_subst (ren (subn^~ 1)) eA).
        asimpl in H9. rewrite er in H9.
        have {}er: (+1) >>> subn_rec^~ 1 = id.
        f_ext. move=>[|x]//.
        pose proof (conv_subst (ren (subn^~ 1)) H9).
        asimpl in H11. rewrite er in H11. asimpl in H11.
        have[Az[t[hs[sbz e]]]]:=var_inv tyv'; subst.
        inv hs. asimpl in sbz.
        have{sbz}[_ sbz]:=ch_inj sbz.
        have{H0}sbz:=conv_trans _ H0 sbz.
        have[eAx _]:=act_inj sbz.
        pose proof (conv_subst (ren (subn^~ 1)) eAx).
        asimpl in H0. rewrite er in H0. asimpl in H0.
        inv k. inv H15.
        have[tyA6[_ tyB6]]:=act_inv ty6.
        have[tyA7[_ tyB7]]:=act_inv ty7.
        have sbi:=conv_trans _ sb6i (conv_sym sb7i).
        asimpl in sbi.
        have[sbAi[sbBi _]]:=act_inj sbi.
        have{}sbAi:=conv_ren_inv sbAi can_cancel2.
        have {}tyv7:Γ9 ⊢ vy : A7 : s4.
        { apply: clc_conv.
          apply: conv_trans.
          apply: H11.
          apply: (conv_sym H0).
          eauto.
          rewrite e8 e5 e1; eauto. }
        have {}tyv6:Γ9 ⊢ vy : A6 : s4.
        { apply: clc_conv.
          apply: conv_sym; eauto.
          eauto.
          rewrite e8 e5 e1; eauto. }
        have tyC6: [Γ] ⊢ B6.[vy/] : Proto : U.
        { destruct s4; simpl in tyB6.
          rewrite<-re_invo in tyB6.
          have mrg:[Γ] ∘ Γ9 => [Γ].
          replace Γ9 with [Γ9].
          rewrite e8 e5 e1. apply: merge_re_id.
          rewrite<-pure_re; eauto.
          have//:=clc_substitution.substitution tyB6 H16 mrg tyv6.
          rewrite<-re_invo in tyB6.
          have//tyB4:=clc_substitution.substitutionN tyB6 tyv. }
        have tyC7: [Γ] ⊢ B7.[vy/] : Proto : U.
        { destruct s4; simpl in tyB7.
          rewrite<-re_invo in tyB7.
          have mrg:[Γ] ∘ Γ9 => [Γ].
          replace Γ9 with [Γ9].
          rewrite e8 e5 e1. apply: merge_re_id.
          rewrite<-pure_re; eauto.
          have//:=clc_substitution.substitution tyB7 H16 mrg tyv7.
          rewrite<-re_invo in tyB7.
          have//:=clc_substitution.substitutionN tyB7 tyv7. }
        have cc:=can_cancel_up can_cancel2. asimpl in cc.
        have eBi:=conv_ren_inv sbBi cc.
        econstructor.
        apply: (erefl (~~r)).
        apply: tyC7.
        apply: context_conv.
        apply: conv_ch.
        apply: conv_subst.
        apply: conv_subst.
        apply: conv_sym; eauto.
        simpl.
        constructor.
        constructor.
        apply: re_pure.
        replace Proto with Proto.[ren (+1)] by autosubst.
        apply: clc_weakening.weakeningN; eauto.
        have mrg:
          Ch (~~r) B6.[vy/].[ren (+1)] :L _: G ∘ _: Ch r B7.[vy/] :L G2 =>
          Ch (~~r) B6.[vy/].[ren (+1)] :L Ch r B7.[vy/] :L Γ.
        repeat constructor; eauto.
        econstructor.
        apply: mrg.
        econstructor; eauto.
        econstructor; eauto. }
      have os:of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity tyv0 os.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//:=clc_linearity.narity ty2 os. inv H5.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity ty1 os. }
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      have[_[e1 e2]]:=merge_re_re H3.
      inv H5.
      have {}wf1:ok (_: Ch r2 A :L Γ1).
      { constructor.
        econstructor; eauto.
        rewrite e1; eauto.
        constructor; eauto.
        apply: re_pure. }
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H2.
      inv mrg.
      have os:of_sort (_: Γ0) 0 None by constructor.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      inv H5.
      have {}wf1:ok (_: _: Γ1).
      { repeat constructor; eauto. }
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H2.
      inv mrg.
      have os:of_sort (_: Γ0) 0 None.
      { repeat constructor. }
      have//=oc:=clc_linearity.narity ty os. } }
  move=>c d v Γ ty wf.
  { inv ty. inv H3. inv H2; inv H4.
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      inv H6.
      have {}wf2:ok (_: _: Γ2).
      repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf2 H2.
      inv mrg. inv H6.
      have os:of_sort (_: _: Γ4) 0 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      have[_[e1 e2]]:=merge_re_re H3.
      inv H6.
      have {}wf2:ok (_: Ch r2 A :L Γ2).
      repeat constructor; eauto.
      rewrite e2; eauto.
      apply: re_pure.
      rewrite e2; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf2 H2.
      inv mrg. inv H6.
      have os:of_sort (_: Ch r2 A :L Γ4) 0 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os.
      have os:of_sort (_: _: Γ4) 0 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      have[e0[e1 e2]]:=merge_re_re H3.
      inv H5. inv H6.
      have//=tyA:=clc_weakening.weakeningN H1.
      have wf1':ok (Ch (~~r2) A.[ren (+1)] :L _: Γ2).
      { econstructor.
        constructor; eauto.
        simpl; rewrite e2.
        constructor; eauto.
        constructor.
        apply: re_pure. }
      have wf2':ok (_: Ch r2 A :L Γ1).
      { constructor.
        econstructor; eauto.
        rewrite e1.
        constructor; eauto.
        apply: re_pure. }
      have{wf1' H4}[G1[G2[B0[t1[mrg1[ty1 h1]]]]]]:=plug_inv wf1' H4.
      inv mrg1; inv H5.
      have /h1{}h1:~Ch (~~r2) A.[ren (+1)] :L _:Γ4 |> U.
      { move=> k. inv k. }
      have{wf2' H2}[G3[G4[B1[t2[mrg2[ty2 h2]]]]]]:=plug_inv wf2' H2.
      inv mrg2; inv H4.
      have /h2{}h2:~_: Ch r2 A :L Γ6 |> U.
      { move=>k. inv k. inv H0. }
      have[_[e4 e5]]:=merge_re_re H6.
      have[_[e6 e7]]:=merge_re_re H5.
      have[wf4 wf5]:=merge_context_ok_inv H6 wf2.
      have[wf6 wf7]:=merge_context_ok_inv H5 wf1.
      have wf3:ok (Ch (~~r2) A.[ren (+1)] :L _: Γ4).
      { econstructor; simpl.
        econstructor; eauto.
        rewrite e4 e2.
        constructor; eauto.
        constructor.
        apply: re_pure. }
      have//=tyB0:=validity wf3 ty1.
      have{ty1}[r3[r4[A4[B4[s3[e[sb2[xor1 ty0]]]]]]]]:=recv_inv ty1; subst.
      have wfB6: ok (Ch r2 A :L Γ6).
      { econstructor; eauto.
        rewrite e6 e1.
        constructor; eauto.
        apply: re_pure. }
      have//=tyB1:=validity (n_ok wfB6) ty2.
      have{ty2}[G1[G2[A2[B2[s1[t[k[sb[mrg[tyS tyv]]]]]]]]]]:=app_inv ty2.
      inv mrg; inv H4.
      have[wf8 wf9]:=merge_context_ok_inv H7 wf6.
      have[_[e8 e9]]:=merge_re_re H7.
      have wfB8:(ok (Ch r2 A :L Γ8)).
      { econstructor; eauto.
        rewrite e8 e6 e1.
        constructor; eauto.
        apply: re_pure. }
      have[_[A'[_ eA']]]:=narity_ren1 wfB8 tyS.
      destruct A'; inv eA'.
      replace (Send (Var 1)) with (Send (Var 0)).[ren (+1)] in tyS by autosubst.
      replace (Pi A'.[ren (+1)] B.[up (ren (+1))] s2 r t0)
        with (Pi A' B s2 r t0).[ren (+1)] in tyS by autosubst.
      move/clc_substitution.strengthen in tyS.
      have[r5[r6[A3[B5[t[e[sb1[xor2 ty1]]]]]]]]:=send_inv tyS; subst.
      have[A2[t0[hs[sb3 e]]]]:=var_inv ty1; subst.
      inv hs. asimpl in sb3.
      have{sb3}[e sb3]:=ch_inj sb3; subst.
      pose proof (conv_subst (ren (+1)) sb3). asimpl in H.
      have[C[t1[hs[sbC e]]]]:=var_inv ty0; subst.
      inv hs. asimpl in sbC.
      have{sb3 sbC}[e sbC]:=ch_inj sbC; subst.
      replace Proto with Proto.[ren (+1)] in tyA by autosubst.
      move/clc_substitution.strengthen in tyA.
      have[A6[B6[ty6[sb6i sb6]]]]:=dual_conv (re_ok wf) H tyA can_cancel2. asimpl in sb6.
      have[A7[B7[ty7[sb7i sb7]]]]:=dual_conv (re_ok wf) sbC tyA can_cancel2. asimpl in sb7.
      asimpl in sb6i. asimpl in sb7i.
      have/act_inj[cA[cB[ex ey]]]:=conv_trans _ sb6i (conv_sym sb7i); subst.
      have{cA}eA:=conv_ren_inv cA can_cancel2.
      have{cB}eB:=conv_ren_inv cB (can_cancel_up can_cancel2).
      have{sb6}[cA1[sb5 _]]:=act_inj sb6.
      have{sb1}[cA2[sb6[ex[ey _]]]]:=pi_inj sb1; subst.
      have wf9': ok (_: Γ9) by constructor.
      have[vx[_[evx _]]]:=narity_ren1 wf9' tyv; subst.
      have tyvx:=clc_substitution.strengthen tyv.
      have[vy[Ay[evy eAy]]]:=narity_ren1 wf9 tyvx; subst.
      have tyvy:=clc_substitution.strengthen tyvx.
      asimpl in sb.
      replace B.[vy.[ren (+2)] .: ren (+1)]
        with B.[vy.[ren (+1)]/].[ren (+1)] in sb by autosubst.
      have//=tyC:=validity wfB8 ty1.
      have{tyC}tyO:=ch_inv tyC.
      have[tyA3[_ tyB5]]:=act_inv tyO.
      have{}tyvx:_: Γ9 ⊢ vy.[ren (+1)] : A3 : s2.
      { apply: clc_conv; simpl.
        apply: (conv_sym cA2).
        eauto.
        rewrite e9. rewrite<-e8; eauto. }
      inv k.
      have[G1[mrg1 mrg2]]:=merge_splitL H5 H7.
      have[G2[mrg3 mrg4]]:=merge_splitR H3 mrg2.
      have[G3[mrg5 mrg6]]:=merge_splitL (merge_sym mrg3) H6.
      have {}tyB5: _: Γ8 ⊢ B5.[vy.[ren (+1)]/] : Proto : U.
      { destruct s2.
        have mrg: _: [Γ8] ∘ _: Γ9 => _: Γ8.
        replace Γ9 with [Γ9].
        constructor.
        rewrite e9. rewrite<-e8.
        rewrite<-pure_re; eauto. apply: merge_pure; eauto.
        inv H8; rewrite<-pure_re; eauto.
        simpl in tyB5. rewrite<-re_invo in tyB5.
        have:=clc_substitution.substitution tyB5 H8 mrg tyvx.
        by asimpl.
        simpl in tyB5. rewrite<-re_invo in tyB5.
        have:=clc_substitution.substitutionN tyB5 tyvx.
        rewrite<-pure_re; eauto. }
      have {}tyB5: _: Γ8 ⊢ Ch r5 B5.[vy.[ren (+1)]/] : Sort L : U.
      { econstructor; eauto. constructor; eauto. }
      have//=wtyB5:=clc_weakening.weakeningN tyB5.
      pose proof (conv_subst (vy.[ren (+1)] .: ids) sb6).
      pose proof (conv_subst (ren (+1)) H2).
      pose proof (conv_subst (vy.[ren (+2)] .: ids) sb5).
      move/(conv_ch r5) in H10.
      asimpl in sb.
      asimpl in H9.
      asimpl in H10.
      have{H2 H9 H10}sb:=conv_trans _ (conv_trans _ H10 H9) sb.
      replace (Ch r5 B6.[vy.[ren (+2)] .: ren (+2)])
        with (Ch r5 B6.[vy/]).[ren (+1)].[ren (+1)] in sb by autosubst.
      have mrgv0:
        _: Ch r5 B6.[vy/] :L Γ8 ∘ _: _: Γ7 => _: Ch r5 B6.[vy/] :L G1.
      { repeat constructor; eauto. }
      have tyv0: _: Ch r5 B6.[vy/] :L Γ8 ⊢ Var 1 : B1 : L.
      { apply: clc_conv; simpl.
        apply: sb.
        repeat constructor; eauto.
        rewrite e8; eauto. }
      have tyc:=h2 _ _ _ mrgv0 tyv0.
      have//=tyC:=validity wf3 ty0.
      have{tyC}tyI:=ch_inv tyC.
      have{tyI}[tyA4[_ tyB4]]:=act_inv tyI.
      have[cA3[sbB _]]:=act_inj sb7.
      have mrgv1:
        Ch (~~r5) B7.[vy/].[ren (+1)] :L _: G3 ∘ _: _: Γ5 =>
        Ch (~~r5) B7.[vy/].[ren (+1)] :L _: G2.
      { repeat constructor; eauto. }
      have cA:Ay.[ren (+1)].[ren (+1)]===A4.
      { pose proof (conv_subst (ren (+1)) cA2). asimpl in H2.
        asimpl.
        apply: conv_trans. apply: (conv_sym H2).
        apply: conv_trans. apply: (conv_sym cA1).
        apply: conv_trans. apply: conv_subst; eauto.
        eauto. }
      pose proof (conv_subst (vy.[ren (+1)].[ren (+1)] .: ids) sbB).
      asimpl in H2=>{sbB}. move: H2=>sbB.
      replace B7.[vy.[ren (+2)] .: ren (+2)]
        with B7.[vy/].[ren (+1)].[ren (+1)] in sbB by autosubst.
      move/(conv_ch (~~r5)) in sbB.
      replace (Ch (~~r5) B7.[vy/].[ren (+1)].[ren (+1)])
        with (Ch (~~r5) B7.[vy/].[ren (+1)]).[ren (+1)] in sbB by autosubst.
      have[_[ex ey]]:=merge_re_re mrg5.
      have tyvz: _: _: Γ9 ⊢ vy.[ren (+2)] : A4 : s2.
      { apply: clc_conv; simpl.
        apply: cA.
        asimpl. by asimpl in tyv.
        rewrite ey. rewrite<-ex; eauto. }
      have {}tyvB4:_: _: [Γ4] ⊢ B4.[vy.[ren (+2)]/] : Proto : U.
      { destruct s2.
        have mrg:_: _: [Γ4] ∘ _: _: Γ9 => _: _: [Γ4].
        repeat constructor.
        replace Γ9 with [Γ9].
        rewrite ey. rewrite<-ex. apply: merge_re_id.
        rewrite<-pure_re; eauto. inv H8; eauto.
        simpl in tyB4. rewrite<-re_invo in tyB4.
        have//:=clc_substitution.substitution tyB4 (key_n H8) mrg tyvz.
        simpl in tyB4. rewrite<-re_invo in tyB4.
        have//=:=clc_substitution.substitutionN tyB4 tyvz. }
      have tyv1:
        Ch (~~r5) B7.[vy/].[ren (+1)] :L _: G3 ⊢
          Pair vy.[ren (+1)].[ren (+1)] (Var 0) L : B0 : L.
      { apply: clc_conv; simpl.
        apply: sb2.
        econstructor; simpl.
        apply: (key_n H8).
        apply: (key_impure (Ch (~~r5) B7.[vy/].[ren (+1)] :L _: Γ4)).
        repeat constructor.
        apply: merge_sym; eauto.
        econstructor; simpl.
        destruct s2; simpl; constructor.
        repeat constructor. apply: re_pure.
        rewrite<-ex; eauto.
        econstructor.
        destruct s2.
        repeat constructor. apply: re_pure.
        repeat constructor. apply: re_pure.
        rewrite<-ex; eauto.
        apply: clc_conv; simpl.
        apply: cA.
        apply: clc_weakening.weakeningN.
        apply: clc_weakening.weakeningN; eauto.
        rewrite ey. rewrite<-ex; eauto.
        asimpl.
        apply: clc_conv; simpl.
        apply: sbB.
        econstructor.
        replace (Ch (~~r5) B7.[vy.[ren (+1)] .: ren (+1)])
          with (Ch (~~r5) B7.[vy/]).[ren (+1)] by autosubst.
        econstructor; eauto.
        econstructor; eauto.
        repeat constructor. apply: re_pure.
        rewrite<-ex; eauto. }
      have tyd:=h1 _ _ _ mrgv1 tyv1.
      have[tyA6[_ tyB6]]:=act_inv ty6.
      have[tyA7[_ tyB7]]:=act_inv ty7.
      have cA0: A6.[ren (+2)] === Ay.[ren (+2)].
      { apply: conv_trans.
        apply: cA1.
        pose proof (conv_subst (ren (+1)) cA2).
        asimpl in H2; eauto. }
      pose proof (conv_subst (ren (subn^~ 2)) cA0)=>{cA0}.
      asimpl in H2. move: H2.
      have->: (+2) >>> subn_rec^~ 2 = id.
      { f_ext. move=>[|x0]; asimpl=>//. }
      move=>cA0. asimpl in cA0.
      have {}tyv6: Γ9 ⊢ vy : A6 : s2.
      { apply: clc_conv.
        apply: (conv_sym cA0).
        eauto.
        rewrite e9 e6 e1; eauto. }
      have {}tyv7: Γ9 ⊢ vy : A7 : s2.
      { apply: clc_conv; eauto.
        rewrite e9 e6 e1; eauto. }
      have {}tyB6: [Γ] ⊢ B6.[vy/] : Proto : U.
      { destruct s2; inv H8.
        have mrg:[Γ] ∘ Γ9 => [Γ].
        replace Γ9 with [Γ9].
        rewrite e9 e6 e1. apply: merge_re_id.
        rewrite<-pure_re; eauto.
        simpl in tyB6. rewrite<-re_invo in tyB6.
        have//:=clc_substitution.substitution tyB6 H9 mrg tyv6.
        simpl in tyB6. rewrite<-re_invo in tyB6.
        have//:=clc_substitution.substitutionN tyB6 tyv6. }
      have {}tyB7: [Γ] ⊢ B7.[vy/] : Proto : U.
      { destruct s2; inv H8.
        have mrg:[Γ] ∘ Γ9 => [Γ].
        replace Γ9 with [Γ9].
        rewrite e9 e6 e1. apply: merge_re_id.
        rewrite<-pure_re; eauto.
        simpl in tyB7. rewrite<-re_invo in tyB7.
        have//:=clc_substitution.substitution tyB7 H9 mrg tyv7.
        simpl in tyB7. rewrite<-re_invo in tyB7.
        have//:=clc_substitution.substitutionN tyB7 tyv7. }
      econstructor.
      apply: (erefl (~~r5)).
      apply: tyB6.
      apply: context_conv.
      apply: conv_ch.
      apply: conv_subst.
      apply: conv_subst.
      apply: eB.
      simpl.
      constructor.
      constructor.
      apply: re_pure.
      replace Proto with Proto.[ren (+1)] by autosubst.
      apply: clc_weakening.weakeningN; eauto.
      have mrg:
        _: Ch r5 B6.[vy/] :L G1 ∘ Ch (~~r5) B7.[vy/].[ren (+1)] :L _: G2 =>
        Ch (~~r5) B7.[vy/].[ren (+1)] :L Ch r5 B6.[vy/] :L Γ.
      { repeat constructor; eauto. }
      econstructor.
      apply: mrg.
      econstructor. apply: tyc.
      econstructor. apply: tyd.
      have os:of_sort (_: _: Γ8) 1 None by repeat constructor.
      have//:=clc_linearity.narity tyS os.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//=oc:=clc_linearity.narity ty2 os.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//=oc:=clc_linearity.narity ty1 os. }
    { have[wf1 wf2]:=merge_context_ok_inv H3 wf.
      inv H5.
      have {}wf1:ok (_: _: Γ1).
      repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H2.
      inv mrg. inv H5.
      have os:of_sort (_: _: Γ4) 1 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os. } }
  move=>c c' d d' e1 e2 Γ ty  wf.
  { inv ty. inv H3.
    inv H5. inv H6.
    inv H2; inv H6.
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf2)) H4.
      inv mrg. inv H6.
      have os:of_sort (_: _: Γ4) 1 None by repeat constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[e0[e1 e2]]:=merge_re_re H5.
      have wfA: ok (Ch (~~r2) A.[ren (+1)] :L _: Γ1).
      econstructor; simpl.
      constructor; eauto.
      have:=clc_weakening.weakeningN H1.
      rewrite e1.
      apply: clc_ch.
      constructor.
      apply: re_pure.
      have wfB: ok (_: Ch r2 A :L Γ2).
      constructor.
      econstructor; simpl; eauto.
      rewrite e2.
      constructor; eauto.
      apply: re_pure.
      have[G1[G2[C1[t1[mrg1[tyC h1]]]]]]:=plug_inv wfA H3.
      have[G3[D4[C2[t2[mrg2[tyW h2]]]]]]:=plug_inv wfB H4.
      inv mrg1; inv H6.
      inv mrg2; inv H6.
      have /h1{}h1 : ~Ch (~~r2) A.[ren (+1)] :L _: Γ4 |> U.
      { move=>k. inv k. }
      have /h2{}h2: ~_: Ch r2 A :L Γ6 |> U.
      { move=>k. inv k. inv H0. }
      have[r3[r4[e[sbC[xor1 ty0]]]]]:=close_inv tyC; subst.
      have[r5[r6[e[sbW[xor2 ty1]]]]]:=wait_inv tyW; subst.
      have[x[tx[hs[_ e]]]]:=var_inv ty0; subst.
      inv hs. inv H0.
      have[y[ty[hs[_ e]]]]:=var_inv ty1; subst.
      inv hs. inv H6.
      have[wf4 wf5]:=merge_context_ok_inv H7 wf1.
      have[wf6 wf7]:=merge_context_ok_inv H8 wf2.
      have[_[e4 e5]]:=merge_re_re H7.
      have[_[e6 e7]]:=merge_re_re H8.
      have wfA4 : ok (Ch (~~r2) A.[ren (+1)] :L _: Γ4).
      { econstructor; simpl.
        constructor; eauto.
        rewrite e4 e1.
        constructor.
        constructor.
        apply: re_pure.
        have//=:=clc_weakening.weakeningN H1; eauto. }
      have wfB6 : ok (_: Ch r2 A :L Γ6).
      { econstructor.
        econstructor; simpl; eauto.
        rewrite e6 e2; eauto.
        constructor; eauto.
        apply: re_pure. }
      have//=tyC1:=validity wfA4 tyC.
      have//=tyC2:=validity wfB6 tyW.
      have mrg1: _: _: Γ4 ∘ _: _: Γ5 => _: _: Γ1 by repeat constructor; eauto.
      have mrg2: _: _: Γ6 ∘ _: _: Γ7 => _: _: Γ2 by repeat constructor; eauto.
      have tyU1: _: _: Γ4 ⊢ It.[ren (+2)] : C1 : U.
      { asimpl.
        apply: clc_conv; simpl.
        apply: sbC.
        repeat constructor; eauto.
        eauto. }
      have tyU2: _: _: Γ6 ⊢ It.[ren (+2)] : C2 : U.
      { asimpl.
        apply: clc_conv; simpl.
        apply: sbW.
        repeat constructor; eauto.
        eauto. }
      have{}h1:=h1 _ _ _ mrg1 tyU1.
      have{}h2:=h2 _ _ _ mrg2 tyU2.
      rewrite eren_comp in h1.
      rewrite eren_comp in h2.
      have[_[A2[_ e]]]:=narity_ren1 (n_ok wf1) h1; subst.
      have[_[A3[_ e]]]:=narity_ren1 (n_ok wf2) h2; subst.
      replace ((c.[It])%C.[ren (+2)])
        with (c.[It]%C.[ren (+1)].[ren (+1)]) in h1 by autosubst.
      replace ((d.[It])%C.[ren (+2)])
        with (d.[It]%C.[ren (+1)].[ren (+1)]) in h2 by autosubst.
      move/clc_substitution.strengthen in h1.
      move/clc_substitution.strengthen in h2.
      have[_[A4[_ e]]]:=narity_ren1 wf1 h1; subst.
      have[_[A5[_ e]]]:=narity_ren1 wf2 h2; subst.
      move/clc_substitution.strengthen in h1.
      move/clc_substitution.strengthen in h2.
      econstructor.
      apply: H5.
      econstructor. apply: h1.
      econstructor. apply: h2.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//:=clc_linearity.narity tyW os.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity tyC os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[_[e1 e2]]:=merge_re_re H5.
      have wf3: ok (Ch r2 A :L Γ1).
      econstructor; eauto.
      rewrite e1; eauto.
      constructor; eauto.
      apply: re_pure.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok wf3) H3.
      inv mrg.
      have os: of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf1)) H3.
      inv mrg.
      have os: of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity ty os. } }
  move=>c c' d d' e1 e2 Γ ty wf.
  { inv ty. inv H3.
    inv H5. inv H6.
    inv H2; inv H6.
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf2)) H4.
      inv mrg. inv H6.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[_[e1 e2]]:=merge_re_re H5.
      have wf3: ok (Ch r2 A :L Γ2).
      econstructor; eauto.
      rewrite e2; eauto.
      constructor; eauto.
      apply: re_pure.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok wf3) H4.
      inv mrg.
      have os: of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[e0[e1 e2]]:=merge_re_re H5.
      have wfA: ok (Ch (~~r2) A.[ren (+1)] :L _: Γ2).
      econstructor; simpl.
      constructor; eauto.
      constructor.
      constructor.
      apply: re_pure.
      replace Proto with Proto.[ren (+1)] by autosubst.
      have:=clc_weakening.weakeningN H1.
      rewrite e2; eauto.
      have wfB: ok (_: Ch r2 A :L Γ1).
      constructor.
      econstructor; simpl; eauto.
      rewrite e1; eauto.
      constructor; eauto.
      apply: re_pure.
      have[G1[G2[C1[t1[mrg1[tyW h1]]]]]]:=plug_inv wfA H4.
      have[G3[D4[C2[t2[mrg2[tyC h2]]]]]]:=plug_inv wfB H3.
      inv mrg1; inv H6.
      inv mrg2; inv H6.
      have /h1{}h1 : ~Ch (~~r2) A.[ren (+1)] :L _: Γ4 |> U.
      { move=>k. inv k. }
      have /h2{}h2: ~_: Ch r2 A :L Γ6 |> U.
      { move=>k. inv k. inv H0. }
      have[r3[r4[e[sbC[xor1 ty0]]]]]:=close_inv tyC; subst.
      have[r5[r6[e[sbW[xor2 ty1]]]]]:=wait_inv tyW; subst.
      have[x[tx[hs[_ e]]]]:=var_inv ty0; subst.
      inv hs. inv H2.
      have[y[ty[hs[_ e]]]]:=var_inv ty1; subst.
      inv hs. inv H2.
      have[wf4 wf5]:=merge_context_ok_inv H7 wf2.
      have[wf6 wf7]:=merge_context_ok_inv H8 wf1.
      have[_[e4 e5]]:=merge_re_re H7.
      have[_[e6 e7]]:=merge_re_re H8.
      have wfA4 : ok (Ch (~~r2) A.[ren (+1)] :L _: Γ4).
      { econstructor; simpl.
        constructor; eauto.
        rewrite e4 e2.
        constructor.
        constructor.
        apply: re_pure.
        have//=:=clc_weakening.weakeningN H1; eauto. }
      have wfB6 : ok (_: Ch r2 A :L Γ6).
      { econstructor.
        econstructor; eauto.
        constructor.
        apply: re_pure.
        rewrite e6 e1; eauto. }
      have//=tyC1:=validity wfA4 tyW.
      have//=tyC2:=validity wfB6 tyC.
      have mrg1: _: _: Γ4 ∘ _: _: Γ5 => _: _: Γ2 by repeat constructor; eauto.
      have mrg2: _: _: Γ6 ∘ _: _: Γ7 => _: _: Γ1 by repeat constructor; eauto.
      have tyU1: _: _: Γ4 ⊢ It.[ren (+2)] : C1 : U.
      { asimpl.
        apply: clc_conv; simpl.
        apply: sbW.
        repeat constructor; eauto.
        eauto. }
      have tyU2: _: _: Γ6 ⊢ It.[ren (+2)] : C2 : U.
      { asimpl.
        apply: clc_conv; simpl.
        apply: sbC.
        repeat constructor; eauto.
        eauto. }
      have{}h1:=h1 _ _ _ mrg1 tyU1.
      have{}h2:=h2 _ _ _ mrg2 tyU2.
      rewrite eren_comp in h1.
      rewrite eren_comp in h2.
      have[_[A2[_ e]]]:=narity_ren1 (n_ok wf2) h1; subst.
      have[_[A3[_ e]]]:=narity_ren1 (n_ok wf1) h2; subst.
      replace ((c.[It])%C.[ren (+2)])
        with (c.[It]%C.[ren (+1)].[ren (+1)]) in h2 by autosubst.
      replace ((d.[It])%C.[ren (+2)])
        with (d.[It]%C.[ren (+1)].[ren (+1)]) in h1 by autosubst.
      move/clc_substitution.strengthen in h1.
      move/clc_substitution.strengthen in h2.
      have[_[A4[_ e]]]:=narity_ren1 wf2 h1; subst.
      have[_[A5[_ e]]]:=narity_ren1 wf1 h2; subst.
      move/clc_substitution.strengthen in h1.
      move/clc_substitution.strengthen in h2.
      econstructor.
      apply: H5.
      econstructor. apply: h2.
      econstructor. apply: h1.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//:=clc_linearity.narity tyC os.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity tyW os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf1)) H3.
      inv mrg. inv H6.
      have os: of_sort (_: _: Γ4) 1 None by repeat constructor.
      have//:=clc_linearity.narity ty os. } }
  move=>m n st Γ ty wf. inv ty.
  { econstructor.
    apply: subject_step; eauto. }
  move=>o p q st ih Γ ty wf. inv ty.
  { have[wf1 wf2]:=merge_context_ok_inv H1 wf.
    econstructor; eauto. }
  move=>p q st ih Γ ty wf. inv ty.
  { econstructor; eauto.
    have tyA:=clc_weakening.weakeningN H1.
    apply: ih; eauto.
    econstructor.
    econstructor; eauto.
    constructor; eauto.
    apply: re_pure.
    simpl.
    constructor.
    constructor.
    apply: re_pure.
    asimpl in tyA; eauto. }
  move=>p p' q q' e1 st ih e2 Γ typ wf.
  { have typ':=congr_type typ e1.
    have tyq':=ih _ typ' wf.
    have//:=congr_type tyq' e2. }
Qed.
