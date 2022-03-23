From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_dual clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness cclc_eval
  clc_linearity cclc_ast cclc_typing cclc_weakening
  cclc_substitution cclc_linearity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dual_sub Γ X Y A1 A2 B1 B2 C1 C2 s1 s2 t1 t2 ξ :
  X ~ Y ->
  X.[ren ξ] <: Out A1 B1 s1 ->
  Y.[ren ξ] <: Inp A2 B2 s2 ->
  [Γ] ⊢ X : C1 : t1 ->
  [Γ] ⊢ Y : C2 : t2 ->
  exists A B3 B4 C3 C4,
    [Γ] ⊢ Out A B3 s1 : C3 : t1 /\
    [Γ] ⊢ Inp A B4 s2 : C4 : t2 /\
    B3 ~ B4 /\ s1 = s2 /\
    (Out A B3 s1).[ren ξ] <: X.[ren ξ] /\
    (Inp A B4 s2).[ren ξ] <: Y.[ren ξ] /\
    (Out A B3 s1).[ren ξ] <: Out A1 B1 s1 /\
    (Inp A B4 s2).[ren ξ] <: Inp A2 B2 s2.
Proof.
  move=>d. elim: d Γ A1 A2 B1 B2 C1 C2 s1 s2 t1 t2 ξ=>{X Y}; asimpl.
  all: try solve[intros; exfalso; solve_sub].
  move=>A B1 B2 s d _ Γ A1 A2 B0 B3 C1 C2 s1 s2 t1 t2 ξ c1 c2 ty1 ty2.
  { exists A. exists B1. exists B2. exists C1. exists C2.
    have[cA1[cB1 e]]:=sub_out_inv c1; subst.
    have[cA2[cB2 e]]:=sub_inp_inv c2; subst.
    repeat split; eauto. }
  move=>m A1 A2 B1 B2 dA ihA dB ihB Γ A0 A3 B0 B3 C1 C2 s1 s2 t1 t2 ξ c1 c2 ty1 ty2.
  { move:c1=>/sub_case_out[A4[B4[r1[r2 r3]]]].
    move:c2=>/sub_case_inp[A5[B5[r4[r5 r6]]]].
    have[G1[G2[Ax[mrgx[_[_[tyA1 tyB1]]]]]]]:=case_inv ty1.
    have[G3[G4[Ay[mrgy[_[_[tyA2 tyB2]]]]]]]:=case_inv ty2.
    have[k1 k2]:=merge_pure_inv mrgx (re_pure _).
    have[k3 k4]:=merge_pure_inv mrgy (re_pure _).
    have[_[e1 e2]]:=merge_re_re mrgx.
    have[_[e3 e4]]:=merge_re_re mrgy.
    rewrite<-re_invo in e1. rewrite<-pure_re in e1; eauto.
    rewrite<-re_invo in e2. rewrite<-pure_re in e2; eauto.
    rewrite<-re_invo in e3. rewrite<-pure_re in e3; eauto.
    rewrite<-re_invo in e4. rewrite<-pure_re in e4; eauto.
    move:r1=>/red_case_out[[hm1 hA]|[hm1 hA]].
    move:r4=>/red_case_inp[[hm2 hB]|[hm2 hB]].
    { have sb1:A1.[ξ >>> ids] <: Out A0 B0 s1.
      { apply: (@sub_trans (Out A4 B4 s1)).
        apply: conv_sub.
        apply: star_conv; eauto.
        apply: sub_out; eauto. }
      have sb2:A2.[ξ >>> ids] <: Inp A3 B3 s2.
      { apply: (@sub_trans (Inp A5 B5 s2)).
        apply: conv_sub.
        apply: star_conv; eauto.
        apply: sub_inp; eauto. }
      rewrite e2 in tyA1.
      rewrite e4 in tyA2.
      have{ihB}ihA:=ihA _ _ _ _ _ _ _ _ _ _ _ _ sb1 sb2 tyA1 tyA2.
      move:ihA=>[A[B6[B7[C3[C4[tyO[tyI[d[e[sb3[sb4[sb5 sb6]]]]]]]]]]]].
      exists A. exists B6. exists B7. exists C3. exists C4.
      repeat split; eauto.
      apply: sub_trans. apply: sb3.
      apply: conv_sub.
      apply: conv_sym.
      apply: star_conv.
      apply: star_trans.
      apply: red_case.
      apply: hm1.
      apply: starR.
      apply: starR.
      apply: star1.
      constructor.
      apply: sub_trans. apply: sb4.
      apply: conv_sub.
      apply: conv_sym.
      apply: star_conv.
      apply: star_trans.
      apply: red_case.
      apply: hm2.
      apply: starR.
      apply: starR.
      apply: star1.
      constructor. }
    { exfalso. apply: red_lr; eauto. }
    move:r4=>/red_case_inp[[hm2 hB]|[hm2 hB]].
    { exfalso. apply: red_lr; eauto. }
    { have sb1:B1.[ξ >>> ids] <: Out A0 B0 s1.
      { apply: (@sub_trans (Out A4 B4 s1)).
        apply: conv_sub.
        apply: star_conv; eauto.
        apply: sub_out; eauto. }
      have sb2:B2.[ξ >>> ids] <: Inp A3 B3 s2.
      { apply: (@sub_trans (Inp A5 B5 s2)).
        apply: conv_sub.
        apply: star_conv; eauto.
        apply: sub_inp; eauto. }
      rewrite e2 in tyB1.
      rewrite e4 in tyB2.
      have{ihA}ihB:=ihB _ _ _ _ _ _ _ _ _ _ _ _ sb1 sb2 tyB1 tyB2.
      move:ihB=>[A[B6[B7[C3[C4[tyO[tyI[d[e[sb3[sb4[sb5 sb6]]]]]]]]]]]].
      exists A. exists B6. exists B7. exists C3. exists C4.
      repeat split; eauto.
      apply: sub_trans. apply: sb3.
      apply: conv_sub.
      apply: conv_sym.
      apply: star_conv.
      apply: star_trans.
      apply: red_case.
      apply: hm1.
      apply: starR.
      apply: starR.
      apply: star1.
      constructor.
      apply: sub_trans. apply: sb4.
      apply: conv_sub.
      apply: conv_sym.
      apply: star_conv.
      apply: star_trans.
      apply: red_case.
      apply: hm2.
      apply: starR.
      apply: starR.
      apply: star1.
      constructor. } }
Qed.

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
    have[G1[G2[A0[B0[C[s0[t0[i[e[sb0[d[mrg[tyA[tyB[tyv tym]]]]]]]]]]]]]]]:=
      fork_inv tyF; subst.
    have[A1[s1[hs[sb1 e]]]]:=var_inv tyv; subst.
    inv hs.
    have/h{}h:~_: _: Γ0 |> U.
    { move=>k. inv k. inv H1.
      have[k1 k2]:=merge_pure_inv mrg H2.
      inv k1. }
    inv mrg. inv H3.
    simpl in tyA. simpl in tyB.
    have//=[l tyB']:=validity wf0 tyF.
    inv wf. inv wf0.
    have[wf1 wf4]:=merge_context_ok_inv H5 H3.
    have[wf5 wf2]:=merge_context_ok_inv H6 H2.
    have[A'[_[eA _]]]:=narity_ren1 (re_ok wf1) tyA.
    destruct A'; inv eA.
    have[B'[_[eB _]]]:=narity_ren1 (re_ok wf4) tyB.
    destruct B'; inv eB.
    have[G[mrg1 mrg2]]:=merge_splitL H6 H5.
    have/h{}h: Ch A'.[ren (+2)] :L _: A2 :L Γ1 ∘ _: _: _: Γ2 => Ch A'.[ren (+2)] :L _: A2 :L G.
    { repeat constructor; eauto. }
    asimpl in h.
    have/h{}h: Ch A'.[ren (+2)] :L _: A2 :L Γ1 ⊢ Pair (Var 0) (Var 2) L : B.[ren (+2)] : L.
    { pose proof (sub_subst (ren (+2)) sb0).
      have[_[e1 e4]]:=merge_re_re H5.
      asimpl in H0.
      have mrg:
        Ch A'.[ren (+2)] :L _: _: [Γ1] ∘ _: _: A2 :L Γ1 => Ch A'.[ren (+2)] :L _: A2 :L Γ1.
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
      repeat constructor.
      apply: clc_conv; simpl.
      apply: sub_sort.
      apply: leq0n.
      repeat constructor. apply: re_pure.
      repeat constructor. apply: re_pure.
      constructor.
      replace (Ch A'.[ren (+2)]) with (Ch A').[ren (+2)] by autosubst.
      replace (Ch A'.[ren (+3)]) with (Ch A').[ren (+2)].[ren (+1)] by autosubst.
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
    have tyv1:_: Ch B'.[ren (+1)] :L _: [Γ4] ⊢ Var 1 : Ch B'.[ren (+3)] : L.
    { replace (Var 1) with (Var 0).[ren (+1)] by autosubst.
      replace (Ch B'.[ren (+3)])
        with (Ch B').[ren (+1)].[ren (+1)].[ren (+1)] by autosubst.
      apply: clc_weakening.weakeningN.
      constructor.
      repeat constructor. apply: re_pure. }
    have mrg:
      _: _: _: Γ4 ∘ _: Ch B'.[ren (+1)] :L _: [Γ4] =>
      _: Ch B'.[ren (+1)] :L _: Γ4.
    { repeat constructor. apply: merge_reR. }
    have k: _: Ch B'.[ren (+1)] :L _: [Γ4] |> L by apply key_impure.
    have tyApp:=clc_app k mrg tym tyv1. asimpl in tyApp.
    have[_[e1 e4]]:=merge_re_re H5.
    have[_[e5 e2]]:=merge_re_re H6.
    econstructor; simpl.
    apply: d.
    rewrite<-e5. rewrite<-e1; eauto.
    rewrite<-e5. rewrite<-e4; eauto.
    asimpl.
    have {}mrg:
      Ch A'.[ren (+2)] :L _: A2 :L G ∘ _: Ch B'.[ren (+1)] :L _: Γ4 =>
      Ch A'.[ren (+2)] :L Ch B'.[ren (+1)] :L A2 :L Γ6.
    { repeat constructor; eauto. }
    econstructor.
    apply: mrg.
    econstructor. apply: h.
    econstructor. apply: tyApp. }
  move=>c d v Γ ty wf.
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
      { econstructor.
        constructor; eauto.
        simpl; rewrite e1; eauto. }
      have wf2':ok (_: Ch B :L Γ2).
      { constructor.
        econstructor; eauto.
        rewrite e2; eauto. }
      have{wf1' H4}[G1[G2[B0[t1[mrg1[ty1 h1]]]]]]:=plug_inv wf1' H4.
      inv mrg1. inv H4.
      have /h1{}h1:~Ch A.[ren (+1)] :L _: Γ4 |> U.
      { move=>k. inv k. }
      have{wf2' H6}[G3[G4[B1[t2[mrg2[ty2 h2]]]]]]:=plug_inv wf2' H6.
      inv mrg2. inv H4.
      have /h2{}h2 :~_: Ch B :L Γ6 |> U.
      { move=>k. inv k. inv H1. }
      have wf3:ok (Ch A.[ren (+1)] :L _: Γ4).
      { have[_[e3 e4]]:=merge_re_re H7.
        econstructor; simpl.
        econstructor.
        have[]//:=merge_context_ok_inv H7 wf1.
        rewrite e3 e1; eauto. }
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
        replace (Ch A.[ren (+1)]) with (Ch A).[ren (+1)] in tyA by autosubst.
        replace (L @ i) with (L @ i).[ren (+1)] in tyA by autosubst.
        move/clc_substitution.strengthen in tyA.
        have{tyA}[iA tyA]:=ch_inv tyA.
        have{H2}[iB tyB]:=ch_inv H2.
        have{tyA tyB iA iB sb3 sb4}
          [A4[B4[B5[C1[C2[tyA[tyB[H[e[sbA[sbB[sb3 sb4]]]]]]]]]]]]:=
          dual_sub H0 sb3 sb4 tyA tyB; subst.
        asimpl in sb3; asimpl in sb4.
        have{sb3}[eA1[sb6 _]]:=sub_out_inv sb3; subst.
        have{sb4}[eA2[sb7 _]]:=sub_inp_inv sb4; subst.
        have {eA0 eA1 eA2}eA:A2 === A'.[ren (+1)].
        apply: conv_trans. apply: (conv_sym eA0).
        apply: conv_trans. apply: (conv_sym eA1).
        apply: eA2.
        have{sb6}sb5:=sub_trans (sub_ch sb6) sb5.
        have{}sb7:=sub_ch sb7.
        pose proof (sub_trans (sub_subst (v .: ids) sb5) sb)=>{sb5}.
        pose proof (sub_subst (v .: ids) sb7)=>{sb7}.
        asimpl in H2. asimpl in H8. inv H4.
        have[wf7 wf8]:=merge_context_ok_inv H7 wf1.
        have[wf9 wf10]:=merge_context_ok_inv H12 wf7.
        have wf11:ok (_: Γ9). repeat constructor; eauto.
        have[vx[Ax[evx eAx]]]:=narity_ren1 wf11 tyv; subst.
        move/clc_substitution.strengthen in tyv.
        have[vy[Ay[evy eAy]]]:=narity_ren1 wf10 tyv; subst.
        move/clc_substitution.strengthen in tyv.
        replace (Ch B4.[vy.[ren (+1)].[ren (+1)] .: ren (+2)])
          with (Ch B4.[vy/].[ren (+1)].[ren (+1)]) in H2 by autosubst.
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
        apply: clc_conv; simpl. apply: H2.
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
        have[Ax eAx]:=narity_ren0 tyA'; subst.
        have er: (+2) >>> subn_rec^~ 1 = (+1).
        f_ext. move=>[|x]//.
        pose proof (sub_subst (ren (subn^~ 1)) sbB).
        asimpl in H1. rewrite er in H1.
        pose proof (conv_subst (ren (subn^~ 1)) eA).
        asimpl in H9. rewrite er in H9.
        have {}er: (+1) >>> subn_rec^~ 1 = id.
        f_ext. move=>[|x]//.
        pose proof (conv_subst (ren (subn^~ 1)) H9).
        asimpl in H11. rewrite er in H11. asimpl in H11.
        have[Az[t[hs[sbz e]]]]:=var_inv tyv'; subst.
        inv hs. asimpl in sbz.
        move/sub_ch_inv in sbz.
        have{H1}sbz:=sub_trans H1 sbz.
        have[eAx _]:=sub_inp_inv sbz.
        pose proof (conv_subst (ren (subn^~ 1)) eAx).
        asimpl in H1. rewrite er in H1. asimpl in H1.
        inv k. inv H15.
        have[i1[tyA4[_ tyB5]]]:=inp_inv tyB.
        have[i2[tyA5[_ tyB6]]]:=out_inv tyA.
        have {}tyv:Γ9 ⊢ vy : A4 : s4.
        { apply: clc_conv.
          apply: conv_sub.
          apply: conv_trans.
          apply: H11.
          apply: (conv_sym H1).
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
  move=>c d v Γ ty wf.
  { inv ty. inv H4. inv H5; inv H6.
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      inv H8.
      have {}wf2:ok (_: _: Γ2).
      repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf2 H4.
      inv mrg. inv H8.
      have os:of_sort (_: _: Γ4) 0 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[_[e1 e2]]:=merge_re_re H5.
      inv H8.
      have {}wf2:ok (_: Ch B :L Γ2).
      repeat constructor; eauto.
      econstructor; eauto.
      rewrite e2; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf2 H4.
      inv mrg. inv H8.
      have os:of_sort (_: Ch B :L Γ4) 0 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os.
      have os:of_sort (_: _: Γ4) 0 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[e0[e1 e2]]:=merge_re_re H5.
      inv H7. inv H8.
      have{H1}//=tyA:=clc_weakening.weakeningN H1.
      have wf1':ok (Ch A.[ren (+1)] :L _: Γ2).
      { econstructor.
        constructor; eauto.
        simpl; rewrite e2; eauto. }
      have wf2':ok (_: Ch B :L Γ1).
      { constructor.
        econstructor; eauto.
        rewrite e1; eauto. }
      have{wf1' H6}[G1[G2[B0[t1[mrg1[ty1 h1]]]]]]:=plug_inv wf1' H6.
      inv mrg1; inv H6.
      have /h1{}h1:~Ch A.[ren (+1)] :L _:Γ4 |> U.
      { move=> k. inv k. }
      have{wf2' H4}[G3[G4[B1[t2[mrg2[ty2 h2]]]]]]:=plug_inv wf2' H4.
      inv mrg2; inv H4.
      have /h2{}h2:~_: Ch B :L Γ6 |> U.
      { move=>k. inv k. inv H1. }
      have[_[e4 e5]]:=merge_re_re H7.
      have[_[e6 e7]]:=merge_re_re H6.
      have[wf4 wf5]:=merge_context_ok_inv H7 wf2.
      have[wf6 wf7]:=merge_context_ok_inv H6 wf1.
      have wf3:ok (Ch A.[ren (+1)] :L _: Γ4).
      { econstructor; simpl.
        econstructor; eauto.
        rewrite e4 e2; eauto. }
      have//=[l tyB0]:=validity wf3 ty1.
      have{ty1}[A4[B4[s3[e[sb2 ty0]]]]]:=recv_inv ty1; subst.
      have wfB6: ok (Ch B :L Γ6).
      { econstructor; eauto. rewrite e6 e1; eauto. }
      have//=[lB1 tyB1]:=validity (n_ok wfB6) ty2.
      have{ty2}[G1[G2[A2[B2[s1[t[k[sb[mrg[tyS tyv]]]]]]]]]]:=app_inv ty2.
      inv mrg; inv H4.
      have[wf8 wf9]:=merge_context_ok_inv H8 wf6.
      have[_[e8 e9]]:=merge_re_re H8.
      have wfB8:(ok (Ch B :L Γ8)).
      { econstructor; eauto. rewrite e8 e6 e1; eauto. }
      have[_[A'[_ eA']]]:=narity_ren1 wfB8 tyS.
      destruct A'; inv eA'.
      replace (Send (Var 1)) with (Send (Var 0)).[ren (+1)] in tyS by autosubst.
      replace (Pi A'.[ren (+1)] B3.[up (ren (+1))] s2 r t0)
        with (Pi A' B3 s2 r t0).[ren (+1)] in tyS by autosubst.
      move/clc_substitution.strengthen in tyS.
      have{tyS}[A3[B5[t[e[sb1 ty1]]]]]:=send_inv tyS; subst.
      have[A2[t0[hs[sb3 e]]]]:=var_inv ty1; subst.
      inv hs. asimpl in sb3.
      move/sub_ch_inv in sb3.
      pose proof (sub_subst (ren (+1)) sb3). asimpl in H.
      have[C[t1[hs[sbC e]]]]:=var_inv ty0; subst.
      inv hs. asimpl in sbC.
      move/sub_ch_inv in sbC.
      replace (Ch A.[ren (+1)]) with (Ch A).[ren (+1)] in tyA by autosubst.
      replace (L @ i) with (L @ i).[ren (+1)] in tyA by autosubst.
      move/clc_substitution.strengthen in tyA.
      have{tyA}[iA tyA]:=ch_inv tyA.
      have{H2}[iB tyB]:=ch_inv H2.
      have{tyA tyB iA iB sb3}
        [A2[B6[B7[C3[C4[tyA[tyB[dx[e[sbA[sbB[sb3 sb4]]]]]]]]]]]]:=
        dual_sub (dual_sym H0) H sbC tyB tyA; subst.
      asimpl in sb3; asimpl in sb4.
      have{sb3}[cA1[sb5 _]]:=sub_out_inv sb3; subst.
      have{sb1}[cA2[sb6[ex[ey _]]]]:=sub_pi_inv sb1; subst.
      have wf9': ok (_: Γ9) by constructor.
      have[vx[_[evx _]]]:=narity_ren1 wf9' tyv; subst.
      have tyvx:=clc_substitution.strengthen tyv.
      have[vy[Ay[evy eAy]]]:=narity_ren1 wf9 tyvx; subst.
      have tyvy:=clc_substitution.strengthen tyvx.
      asimpl in sb.
      replace B3.[vy.[ren (+2)] .: ren (+1)]
        with B3.[vy.[ren (+1)]/].[ren (+1)] in sb by autosubst.
      have//=[l0 tyC]:=validity wfB8 ty1.
      have{l0 tyC}[l0 tyO]:=ch_inv tyC.
      have{l0 tyO}[l0[tyA3[_ tyB5]]]:=out_inv tyO.
      have{}tyvx:_: Γ9 ⊢ vy.[ren (+1)] : A3 : s2.
      { apply: clc_conv; simpl.
        apply: conv_sub.
        apply: (conv_sym cA2).
        eauto.
        rewrite e9. rewrite<-e8; eauto. }
      inv k.
      have[G1[mrg1 mrg2]]:=merge_splitL H6 H8.
      have[G2[mrg3 mrg4]]:=merge_splitR H5 mrg2.
      have[G3[mrg5 mrg6]]:=merge_splitL (merge_sym mrg3) H7.
      have {}tyB5: _: Γ8 ⊢ B5.[vy.[ren (+1)]/] : Proto l0 : U.
      { destruct s2.
        have mrg: _: [Γ8] ∘ _: Γ9 => _: Γ8.
        replace Γ9 with [Γ9].
        constructor.
        rewrite e9. rewrite<-e8.
        rewrite<-pure_re; eauto. apply: merge_pure; eauto.
        inv H3; rewrite<-pure_re; eauto.
        have:=clc_substitution.substitution tyB5 H3 mrg tyvx.
        by asimpl.
        have:=clc_substitution.substitutionN tyB5 tyvx.
        rewrite<-pure_re; eauto. }
      have {}tyB5: _: Γ8 ⊢ Ch B5.[vy.[ren (+1)]/] : L @ l0 : U.
      { econstructor; eauto. constructor; eauto. }
      have//=tyB6:=clc_weakening.weakeningN tyB5.
      pose proof (sub_subst (vy.[ren (+1)] .: ids) sb6).
      pose proof (sub_subst (ren (+1)) H2).
      pose proof (sub_subst (vy.[ren (+2)] .: ids) sb5).
      move/sub_ch in H10.
      asimpl in sb.
      asimpl in H9.
      asimpl in H10.
      have {H2 H9 H10}sb:=sub_trans (sub_trans H10 H9) sb.
      replace (Ch B6.[vy.[ren (+2)] .: ren (+2)])
        with (Ch B6.[vy/]).[ren (+1)].[ren (+1)] in sb by autosubst.
      have mrgv0:
        _: Ch B6.[vy/] :L Γ8 ∘ _: _: Γ7 => _: Ch B6.[vy/] :L G1.
      { repeat constructor; eauto. }
      have tyv0: _: Ch B6.[vy/] :L Γ8 ⊢ Var 1 : B1 : L.
      { apply: clc_conv; simpl.
        apply: sb.
        repeat constructor; eauto.
        rewrite e8; eauto. }
      have tyc:=h2 _ _ _ mrgv0 tyv0.
      have//=[l1 tyC]:=validity wf3 ty0.
      have{l1 tyC}[l1 tyI]:=ch_inv tyC.
      have{l1 tyI}[l1[tyA4[_ tyB4]]]:=inp_inv tyI.
      have{}sbI:=sub_trans sbB sbC. asimpl in sbI.
      have{sbB}[cA3[sbB _]]:=sub_inp_inv sbI; subst.
      have mrgv1:
        Ch B7.[vy/].[ren (+1)] :L _: G3 ∘ _: _: Γ5 => Ch B7.[vy/].[ren (+1)] :L _: G2.
      { repeat constructor; eauto. }
      have cA:Ay.[ren (+1)].[ren (+1)]===A4.
      { pose proof (conv_subst (ren (+1)) cA2). asimpl in H2.
        asimpl.
        apply: conv_trans. apply: (conv_sym H2).
        apply: conv_trans. apply: (conv_sym cA1).
        eauto. }
      pose proof (sub_subst (vy.[ren (+1)].[ren (+1)] .: ids) sbB).
      asimpl in H2=>{sbB}. move: H2=>sbB.
      replace B7.[vy.[ren (+2)] .: ren (+2)]
        with B7.[vy/].[ren (+1)].[ren (+1)] in sbB by autosubst.
      move/sub_ch in sbB.
      replace (Ch B7.[vy/].[ren (+1)].[ren (+1)])
        with (Ch B7.[vy/].[ren (+1)]).[ren (+1)] in sbB by autosubst.
      have[_[ex ey]]:=merge_re_re mrg5.
      have tyvz: _: _: Γ9 ⊢ vy.[ren (+2)] : A4 : s2.
      { apply: clc_conv; simpl.
        apply: conv_sub.
        apply: cA.
        asimpl. by asimpl in tyv.
        rewrite ey. rewrite<-ex; eauto. }
      have {}tyvB4:_: _: [Γ4] ⊢ B4.[vy.[ren (+2)]/] : Proto l1 : U.
      { destruct s2.
        have mrg:_: _: [Γ4] ∘ _: _: Γ9 => _: _: [Γ4].
        repeat constructor.
        replace Γ9 with [Γ9].
        rewrite ey. rewrite<-ex. apply: merge_re_id.
        rewrite<-pure_re; eauto. inv H3; eauto.
        have//:=clc_substitution.substitution tyB4 (key_n H3) mrg tyvz.
        have//=:=clc_substitution.substitutionN tyB4 tyvz. }
      have tyv1:
        Ch B7.[vy/].[ren (+1)] :L _: G3 ⊢ Pair vy.[ren (+1)].[ren (+1)] (Var 0) L : B0 : L.
      { apply: clc_conv; simpl.
        apply: sb2.
        econstructor; simpl.
        apply: (key_n H3).
        apply: (key_impure (Ch B7.[vy/].[ren (+1)] :L _: Γ4)).
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
        rewrite<-re_invo.
        rewrite<-ex; eauto.
        apply: clc_conv; simpl.
        apply: conv_sub.
        apply: cA.
        apply: clc_weakening.weakeningN.
        apply: clc_weakening.weakeningN; eauto.
        rewrite ey. rewrite<-ex; eauto.
        asimpl.
        apply: clc_conv; simpl.
        apply: sbB.
        econstructor.
        replace (Ch B7.[vy.[ren (+1)] .: ren (+1)])
          with (Ch B7.[vy/]).[ren (+1)] by autosubst.
        econstructor; eauto.
        econstructor; eauto.
        repeat constructor. apply: re_pure.
        rewrite<-ex; eauto. }
      have tyd:=h1 _ _ _ mrgv1 tyv1.
      have dv:B6.[vy/] ~ B7.[vy/].
      { apply: dual_subst; eauto. }
      have[x[tyA2x[_ tyB2]]]:=out_inv tyA.
      have[y[tyA2y[_ tyB7]]]:=inp_inv tyB.
      have cA0: A2.[ren (+2)] === Ay.[ren (+2)].
      { apply: conv_trans.
        apply: cA1.
        pose proof (conv_subst (ren (+1)) cA2).
        asimpl in H2; eauto. }
      pose proof (conv_subst (ren (subn^~ 2)) cA0)=>{cA0}.
      asimpl in H2. move: H2.
      have->: (+2) >>> subn_rec^~ 2 = id.
      { f_ext. move=>[|x0]; asimpl=>//. }
      move=>cA0. asimpl in cA0.
      have {}tyv: Γ9 ⊢ vy : A2 : s2.
      { apply: clc_conv.
        apply: conv_sub.
        apply: (conv_sym cA0).
        eauto.
        rewrite e9 e6 e1; eauto. }
      have {}tyB2: [Γ] ⊢ Ch B6.[vy/] : L @ (maxn x y) : U.
      { apply: clc_conv.
        apply: sub_sort.
        apply: leq_maxl.
        econstructor. apply:re_pure.
        destruct s2; inv H3.
        have mrg:[Γ] ∘ Γ9 => [Γ].
        replace Γ9 with [Γ9].
        rewrite e9 e6 e1. apply: merge_re_id.
        rewrite<-pure_re; eauto.
        have//:=clc_substitution.substitution tyB2 H9 mrg tyv.
        have//:=clc_substitution.substitutionN tyB2 tyv.
        constructor. apply: re_pure. }
      have {}tyB7: [Γ] ⊢ Ch B7.[vy/] : L @ (maxn x y) : U.
      { apply: clc_conv.
        apply: sub_sort.
        apply: leq_maxr.
        econstructor. apply:re_pure.
        destruct s2; inv H3.
        have mrg:[Γ] ∘ Γ9 => [Γ].
        replace Γ9 with [Γ9].
        rewrite e9 e6 e1. apply: merge_re_id.
        rewrite<-pure_re; eauto.
        have//:=clc_substitution.substitution tyB7 H9 mrg tyv.
        have//:=clc_substitution.substitutionN tyB7 tyv.
        constructor. apply: re_pure. }
      econstructor.
      apply: (dual_sym dv).
      apply: tyB7.
      apply: tyB2.
      have mrg:
        _: Ch B6.[vy/] :L G1 ∘ Ch B7.[vy/].[ren (+1)] :L _: G2 =>
        Ch B7.[vy/].[ren (+1)] :L Ch B6.[vy/] :L Γ.
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
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      inv H7.
      have {}wf1:ok (_: _: Γ1).
      repeat constructor; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H4.
      inv mrg. inv H7.
      have os:of_sort (_: _: Γ4) 1 None.
      repeat constructor; eauto.
      have//=oc:=clc_linearity.narity ty os. } }
  move=>c c' d d' e1 e2 Γ ty  wf.
  { inv ty. inv H4.
    inv H7. inv H8.
    inv H5; inv H8.
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf2)) H6.
      inv mrg. inv H8.
      have os:of_sort (_: _: Γ4) 1 None by repeat constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[e0[e1 e2]]:=merge_re_re H7.
      have wfA: ok (Ch A.[ren (+1)] :L _: Γ1).
      econstructor; simpl.
      constructor; eauto.
      have:=clc_weakening.weakeningN H1.
      rewrite e1; eauto.
      have wfB: ok (_: Ch B :L Γ2).
      constructor.
      econstructor; simpl; eauto.
      rewrite e2; eauto.
      have[G1[G2[C1[t1[mrg1[tyC h1]]]]]]:=plug_inv wfA H4.
      have[G3[D4[C2[t2[mrg2[tyW h2]]]]]]:=plug_inv wfB H6.
      inv mrg1; inv H8.
      inv mrg2; inv H8.
      have /h1{}h1 : ~Ch A.[ren (+1)] :L _: Γ4 |> U.
      { move=>k. inv k. }
      have /h2{}h2: ~_: Ch B :L Γ6 |> U.
      { move=>k. inv k. inv H3. }
      have[e[sbC ty0]]:=close_inv tyC; subst.
      have[e[sbW ty1]]:=wait_inv tyW; subst.
      have[x[tx[hs[_ e]]]]:=var_inv ty0; subst.
      inv hs. inv H3.
      have[y[ty[hs[_ e]]]]:=var_inv ty1; subst.
      inv hs. inv H8.
      have[wf4 wf5]:=merge_context_ok_inv H9 wf1.
      have[wf6 wf7]:=merge_context_ok_inv H10 wf2.
      have[_[e4 e5]]:=merge_re_re H9.
      have[_[e6 e7]]:=merge_re_re H10.
      have wfA4 : ok (Ch A.[ren (+1)] :L _: Γ4).
      { econstructor; simpl.
        constructor; eauto.
        rewrite e4 e1.
        have//=:=clc_weakening.weakeningN H1; eauto. }
      have wfB6 : ok (_: Ch B :L Γ6).
      { econstructor.
        econstructor; simpl; eauto.
        rewrite e6 e2; eauto. }
      have//=[l1 tyC1]:=validity wfA4 tyC.
      have//=[l2 tyC2]:=validity wfB6 tyW.
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
      apply: H7.
      econstructor. apply: h1.
      econstructor. apply: h2.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//:=clc_linearity.narity tyW os.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity tyC os. }
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[_[e1 e2]]:=merge_re_re H7.
      have wf3: ok (Ch B :L Γ1).
      econstructor; eauto.
      rewrite e1; eauto.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok wf3) H4.
      inv mrg.
      have os: of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf1)) H4.
      inv mrg.
      have os: of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity ty os. } }
  move=>c c' d d' e1 e2 Γ ty wf.
  { inv ty. inv H4.
    inv H7. inv H8.
    inv H5; inv H8.
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf2)) H6.
      inv mrg. inv H8.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[_[e1 e2]]:=merge_re_re H7.
      have wf3: ok (Ch B :L Γ2).
      econstructor; eauto.
      rewrite e2; eauto.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok wf3) H6.
      inv mrg.
      have os: of_sort (_: Γ0) 0 None by constructor.
      have//:=clc_linearity.narity ty os. }
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[e0[e1 e2]]:=merge_re_re H7.
      have wfA: ok (Ch A.[ren (+1)] :L _: Γ2).
      econstructor; simpl.
      constructor; eauto.
      have:=clc_weakening.weakeningN H1.
      rewrite e2; eauto.
      have wfB: ok (_: Ch B :L Γ1).
      constructor.
      econstructor; simpl; eauto.
      rewrite e1; eauto.
      have[G1[G2[C1[t1[mrg1[tyW h1]]]]]]:=plug_inv wfA H6.
      have[G3[D4[C2[t2[mrg2[tyC h2]]]]]]:=plug_inv wfB H4.
      inv mrg1; inv H8.
      inv mrg2; inv H8.
      have /h1{}h1 : ~Ch A.[ren (+1)] :L _: Γ4 |> U.
      { move=>k. inv k. }
      have /h2{}h2: ~_: Ch B :L Γ6 |> U.
      { move=>k. inv k. inv H3. }
      have[e[sbC ty0]]:=close_inv tyC; subst.
      have[e[sbW ty1]]:=wait_inv tyW; subst.
      have[x[tx[hs[_ e]]]]:=var_inv ty0; subst.
      inv hs. inv H5.
      have[y[ty[hs[_ e]]]]:=var_inv ty1; subst.
      inv hs. inv H5.
      have[wf4 wf5]:=merge_context_ok_inv H9 wf2.
      have[wf6 wf7]:=merge_context_ok_inv H10 wf1.
      have[_[e4 e5]]:=merge_re_re H9.
      have[_[e6 e7]]:=merge_re_re H10.
      have wfA4 : ok (Ch A.[ren (+1)] :L _: Γ4).
      { econstructor; simpl.
        constructor; eauto.
        rewrite e4 e2.
        have//=:=clc_weakening.weakeningN H1; eauto. }
      have wfB6 : ok (_: Ch B :L Γ6).
      { econstructor.
        econstructor; simpl; eauto.
        rewrite e6 e1; eauto. }
      have//=[l1 tyC1]:=validity wfA4 tyW.
      have//=[l2 tyC2]:=validity wfB6 tyC.
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
      apply: H7.
      econstructor. apply: h2.
      econstructor. apply: h1.
      have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
      have//:=clc_linearity.narity tyC os.
      have os:of_sort (_: _: Γ4) 0 None by constructor.
      have//:=clc_linearity.narity tyW os. }
    { have[wf1 wf2]:=merge_context_ok_inv H7 wf.
      have[G1[G2[B0[t[mrg[ty _]]]]]]:=plug_inv (n_ok (n_ok wf1)) H4.
      inv mrg. inv H8.
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
    asimpl in tyA; eauto. }
  move=>p p' q q' e1 st ih e2 Γ typ wf.
  { have typ':=congr_type typ e1.
    have tyq':=ih _ typ' wf.
    have//:=congr_type tyq' e2. }
Qed.
