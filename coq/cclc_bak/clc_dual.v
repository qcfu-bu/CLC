From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dual : term -> term -> Prop :=
| dual_end : dual InpEnd OutEnd
| dual_endi : dual OutEnd InpEnd
| dual_com A B1 B2 s :
  dual B1 B2 ->
  dual (Inp A B1 s) (Out A B2 s)
| dual_comi A B1 B2 s :
  dual B1 B2 ->
  dual (Out A B1 s) (Inp A B2 s)
| dual_case m A1 A2 B1 B2 :
  dual A1 A2 ->
  dual B1 B2 ->
  dual (Case m A1 B1) (Case m A2 B2).

Notation "m ~ n" := (dual m n) (at level 30).

Lemma dual_sym A B : A ~ B -> B ~ A.
Proof.
  elim; eauto using dual.
Qed.

Lemma dual_inj A B C :
  A ~ B -> A ~ C -> B = C.
Proof.
  move=>h.
  elim: h C=>{A B}.
  move=>C d. inv d; eauto.
  move=>C d. inv d; eauto.
  move=>A B1 B2 s d1 ih C d2. inv d2.
  have->//:=ih _ H3.
  move=>A B1 B2 s d1 ih C d2. inv d2.
  have->//:=ih _ H3.
  move=>m A1 A2 B1 B2 dA ihA dB ihB C d. inv d.
  have->:=ihA _ H3.
  have->//:=ihB _ H4.
Qed.

Lemma dual_subst A B σ : A ~ B -> A.[σ] ~ B.[σ].
Proof with eauto using dual.
  move=>d. elim: d σ=>{A B}...
Qed.

Lemma rename_dual A B ξ : A ~ B -> A.[ren ξ] ~ B.[ren ξ].
Proof with eauto using dual.
  apply: dual_subst.
Qed.

Lemma red_cases m n1 n2 x :
  Case m n1 n2 ~>* x ->
  (exists m' n1' n2', x = Case m' n1' n2' /\ m ~>* m' /\ n1 ~>* n1' /\ n2 ~>* n2') \/
  (m ~>* Left /\ n1 ~>* x) \/ (m ~>* Right /\ n2 ~>* x).
Proof.
  elim=>{x}.
  left. exists m. exists n1. exists n2. eauto.
  move=>y z rd [h|[h|h]] st.
  { move:h=>[m'[n1'[n2'[e1[r1[r2 r3]]]]]]; subst. inv st.
    { left.
      exists m'0. exists n1'. exists n2'.
      repeat split; eauto.
      apply: star_trans; eauto.
      apply: star1; eauto. }
    { left.
      exists m'. exists n1'0. exists n2'.
      repeat split; eauto.
      apply: star_trans; eauto.
      apply: star1; eauto. }
    { left.
      exists m'. exists n1'. exists n2'0.
      repeat split; eauto.
      apply: star_trans; eauto.
      apply: star1; eauto. }
    { right. left. eauto. }
    { right. right. eauto. } }
  { move:h=>[r1 r2].
    right. left.
    split; eauto.
    apply: star_trans; eauto.
    apply: star1; eauto. }
  { move:h=>[r1 r2].
    right. right.
    split; eauto.
    apply: star_trans; eauto.
    apply: star1; eauto. }
Qed.

Lemma red_case_out m n1 n2 A B s :
  Case m n1 n2 ~>* Out A B s ->
  (m ~>* Left /\ n1 ~>* Out A B s) \/ (m ~>* Right /\ n2 ~>* Out A B s).
Proof.
  move=>/red_cases[h|[h|h]].
  { move:h=>[m'[n1'[n2'[e _]]]]. inv e. }
  { left; eauto. }
  { right; eauto. }
Qed.

Lemma red_case_inp m n1 n2 A B s :
  Case m n1 n2 ~>* Inp A B s ->
  (m ~>* Left /\ n1 ~>* Inp A B s) \/ (m ~>* Right /\ n2 ~>* Inp A B s).
Proof.
  move=>/red_cases[h|[h|h]].
  { move:h=>[m'[n1'[n2'[e _]]]]. inv e. }
  { left; eauto. }
  { right; eauto. }
Qed.

Lemma red_lr m : ~(m ~>* Left /\ m ~>* Right).
Proof.
  move=>[r1 r2].
  have[x r3 r4]:=confluence r1 r2.
  have e:=red_left_inv r3; subst.
  have e:=red_right_inv r4; subst.
  inv e.
Qed.

Lemma conv_case_out m n1 n2 A B s :
  Case m n1 n2 === Out A B s ->
  exists A' B', Case m n1 n2 ~>* Out A' B' s /\ A ~>* A' /\ B ~>* B'.
Proof.
  move=>/church_rosser[x r1 r2].
  have[A'[B'[rA[rB e]]]]:=red_out_inv r2; subst.
  exists A'. exists B'. eauto.
Qed.

Lemma conv_case_inp m n1 n2 A B s :
  Case m n1 n2 === Inp A B s ->
  exists A' B', Case m n1 n2 ~>* Inp A' B' s /\ A ~>* A' /\ B ~>* B'.
Proof.
  move=>/church_rosser[x r1 r2].
  have[A'[B'[rA[rB e]]]]:=red_inp_inv r2; subst.
  exists A'. exists B'. eauto.
Qed.

Lemma sub_case_out m n1 n2 A B s :
  Case m n1 n2 <: Out A B s ->
  exists A' B', Case m n1 n2 ~>* Out A' B' s /\ A' === A /\ B' <: B.
Proof.
  move=>[A' B' sb e1 e2].
  inv sb; try solve[exfalso; solve_conv].
  { have/conv_case_out[Ax[Bx[r1[r2 r3]]]]:Case m n1 n2 === Out A B s.
    apply:conv_trans; eauto.
    exists Ax. exists Bx.
    repeat split; eauto.
    apply: conv_sym. apply: star_conv. eauto.
    apply: conv_sub. apply: conv_sym. apply: star_conv. eauto. }
  { have[Ax[Bx[r1[r2 r3]]]]:=conv_case_out e1.
    have[eA[eB e]]:=out_inj e2; subst.
    exists Ax. exists Bx.
    repeat split; eauto.
    apply: conv_trans.
    apply: conv_sym.
    apply: star_conv; eauto.
    eauto.
    have eB':=star_conv r3.
    apply: SubI.
    apply: H.
    apply: conv_sym; eauto.
    eauto. }
Qed.

Lemma sub_case_inp m n1 n2 A B s :
  Case m n1 n2 <: Inp A B s ->
  exists A' B', Case m n1 n2 ~>* Inp A' B' s /\ A' === A /\ B' <: B.
Proof.
  move=>[A' B' sb e1 e2].
  inv sb; try solve[exfalso; solve_conv].
  { have/conv_case_inp[Ax[Bx[r1[r2 r3]]]]:Case m n1 n2 === Inp A B s.
    apply:conv_trans; eauto.
    exists Ax. exists Bx.
    repeat split; eauto.
    apply: conv_sym. apply: star_conv. eauto.
    apply: conv_sub. apply: conv_sym. apply: star_conv. eauto. }
  { have[Ax[Bx[r1[r2 r3]]]]:=conv_case_inp e1.
    have[eA[eB e]]:=inp_inj e2; subst.
    exists Ax. exists Bx.
    repeat split; eauto.
    apply: conv_trans.
    apply: conv_sym.
    apply: star_conv; eauto.
    eauto.
    have eB':=star_conv r3.
    apply: SubI.
    apply: H.
    apply: conv_sym; eauto.
    eauto. }
Qed.

Lemma dual_sub X Y A1 A2 B1 B2 s1 s2 ξ :
  X ~ Y ->
  X.[ren ξ] <: Out A1 B1 s1 ->
  Y.[ren ξ] <: Inp A2 B2 s2 ->
  exists A B3 B4,
    B3 ~ B4 /\ s1 = s2 /\
    (Out A B3 s1).[ren ξ] <: Out A1 B1 s1 /\
    (Inp A B4 s2).[ren ξ] <: Inp A2 B2 s2.
Proof.
  move=>d. elim: d A1 A2 B1 B2 s1 s2 ξ=>{X Y}; asimpl.
  all: try solve[intros; exfalso; solve_sub].
  move=>A B1 B2 s d _ A1 A2 B0 B3 s1 s2 ξ c1 c2.
  { exists A. exists B1. exists B2.
    have[cA1[cB1 e]]:=sub_out_inv c1; subst.
    have[cA2[cB2 e]]:=sub_inp_inv c2; subst.
    repeat split; eauto. }
  move=>m A1 A2 B1 B2 dA ihA dB ihB A0 A3 B0 B3 s1 s2 ξ c1 c2.
  { move:c1=>/sub_case_out[A4[B4[r1[r2 r3]]]].
    move:c2=>/sub_case_inp[A5[B5[r4[r5 r6]]]].
    move:r1=>/red_case_out[[hm1 hA]|[hm1 hA]].
    move:r4=>/red_case_inp[[hm2 hB]|[hm2 hB]].
    apply: ihA; eauto.
    apply: (@sub_trans (Out A4 B4 s1)).
    apply: conv_sub.
    apply: star_conv; eauto.
    apply: sub_out; eauto.
    apply: (@sub_trans (Inp A5 B5 s2)).
    apply: conv_sub.
    apply: star_conv; eauto.
    apply: sub_inp; eauto.
    exfalso. apply: red_lr; eauto.
    move:r4=>/red_case_inp[[hm2 hB]|[hm2 hB]].
    exfalso. apply: red_lr; eauto.
    apply: ihB; eauto.
    apply: (@sub_trans (Out A4 B4 s1)).
    apply: conv_sub.
    apply: star_conv; eauto.
    apply: sub_out; eauto.
    apply: (@sub_trans (Inp A5 B5 s2)).
    apply: conv_sub.
    apply: star_conv; eauto.
    apply: sub_inp; eauto. }
Qed.
