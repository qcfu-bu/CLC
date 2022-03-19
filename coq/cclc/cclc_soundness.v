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
      have[_[e1 e2]]:=merge_re_re H5.
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
      have[G1[G2[B0[t1[mrg1[ty1 h1]]]]]]:=plug_inv wf1' H4.
      inv mrg1; inv H7.
      { have /h1{}h1:~Ch A.[ren (+1)] :L _: Γ4 |> U.
          move=>k. inv k.
        have[G3[G4[B1[t2[mrg2[ty2 h2]]]]]]:=plug_inv wf2' H6.
        inv mrg2. inv H7.
        { have /h2{}h2 :~_: Ch B :L Γ6 |> U.
            move=>k. inv k. inv H1.
          have[G1[G2[A2[B2[s1[t[sb[mrg[tyS tyv]]]]]]]]]:=app_inv ty1.
          have[A3[B3[t0 tyv0]]]:=send_inv tyS.
          have[A4[B4[t3 tyv1]]]:=recv_inv ty2.
          admit.

        }
        { have os:of_sort (_: _: Γ6) 1 None by repeat constructor.
          have//:=clc_linearity.narity ty2 os. } }
      { have os:of_sort (_: _: Γ4) 0 None by constructor.
        have//:=clc_linearity.narity ty1 os. } }
    { have[wf1 wf2]:=merge_context_ok_inv H5 wf.
      have[_[e1 e2]]:=merge_re_re H5.
      inv H7.
      have {}wf1:ok (_: Ch B :L Γ1).
        constructor.
        econstructor; eauto.
        rewrite e1; eauto.
      have[G1[G2[B0[t[mrg[ty h]]]]]]:=plug_inv wf1 H4.
      inv mrg.
      have os:of_sort (_: Γ0) 0 None by constructor.
      have//=oc:=clc_linearity.narity ty os. }
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
