From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_resolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value : term -> Prop :=
| value_sort s l :
  value (Sort s l)
| value_pi A B s t :
  value (Pi A B s t)
| value_lam A m s t :
  value (Lam A m s t)
| value_unit :
  value Unit
| value_it :
  value It
| value_sigma A B s r t :
  value (Sigma A B s r t)
| value_pair m n t :
  value m ->
  value n ->
  value (Pair m n t).

Inductive cbv_step : term -> term -> Prop :=
| cbv_appL m m' n :
  cbv_step m m' ->
  cbv_step (App m n) (App m' n)
| cbv_appR m n n' :
  value m ->
  cbv_step (App m n) (App m n')
| cbv_beta A m n s t :
  value n ->
  cbv_step (App (Lam A m s t) n) m.[n/]
| cbv_pairL m m' n t :
  cbv_step m m' ->
  cbv_step (Pair m n t) (Pair m' n t)
| cbv_pairR m n n' t :
  value m ->
  cbv_step n n' ->
  cbv_step (Pair m n t) (Pair m n' t)
| cbv_letin1 m m' n :
  cbv_step m m' ->
  cbv_step (LetIn1 m n) (LetIn1 m' n)
| cbv_iota1 n :
  cbv_step (LetIn1 It n) n
| cbv_letin2 m m' n :
  cbv_step m m' ->
  cbv_step (LetIn2 m n) (LetIn2 m' n)
| cbv_iota2 m1 m2 n t :
  cbv_step (LetIn2 (Pair m1 m2 t) n) n.[m2,m1/].

Inductive eval : context term -> term -> context term -> term -> Prop :=
| eval_sort Θ s i l :
  l = length Θ ->
  eval Θ (Sort s i) (Sort s i :U Θ) (Ptr l)
| eval_pi Θ A B s t l :
  l = length Θ ->
  eval Θ (Pi A B s t) (Pi A B s t :U Θ) (Ptr l)
| eval_lam Θ A m s t l :
  l = length Θ ->
  eval Θ (Lam A m s t) (Lam A m s t :{t} Θ) (Ptr l)
| eval_appL Θ Θ' m m' n :
  eval Θ m Θ' m' ->
  eval Θ (App m n) Θ' (App m' n)
| eval_appR Θ Θ' l n n' :
  eval Θ n Θ' n' ->
  eval Θ (App (Ptr l) n) Θ' (App (Ptr l) n')
| eval_beta Θ Θ' lf la A m s t :
  free Θ lf (Lam A m s t) Θ' ->
  eval Θ (App (Ptr lf) (Ptr la)) Θ' m.[Ptr la/]
| eval_unit Θ l :
  l = length Θ ->
  eval Θ Unit (Unit :U Θ) (Ptr l)
| eval_it Θ l :
  l = length Θ ->
  eval Θ It (It :U Θ) (Ptr l)
| eval_sigma Θ A B s r t l :
  l = length Θ ->
  eval Θ (Sigma A B s r t) (Sigma A B s r t :U Θ) (Ptr l)
| eval_pairL Θ Θ' m m' n t :
  eval Θ m Θ' m' ->
  eval Θ (Pair m n t) Θ' (Pair m' n t)
| eval_pairR Θ Θ' l n n' t :
  eval Θ n Θ' n' ->
  eval Θ (Pair (Ptr l) n t) Θ' (Pair (Ptr l) n' t)
| eval_pairV Θ l lm ln t :
  l = length Θ ->
  eval Θ (Pair (Ptr lm) (Ptr ln) t)
         ((Pair (Ptr lm) (Ptr ln) t) :{t} Θ) (Ptr l)
| eval_letin1 Θ Θ' m m' n :
  eval Θ m Θ' m' ->
  eval Θ (LetIn1 m n) Θ' (LetIn1 m' n)
| eval_iota1 Θ Θ' l n :
  free Θ l It Θ' ->
  eval Θ (LetIn1 (Ptr l) n) Θ' n
| eval_iota2 Θ Θ' lm ln l n t :
  free Θ l (Pair (Ptr lm) (Ptr ln) t) Θ' ->
  eval Θ (LetIn2 (Ptr l) n) Θ' n.[Ptr ln,Ptr ln/].


Lemma eval_split Θ1 Θ2 Θ Θ' Γ m n m' A :
  ok Γ -> well_resolved Θ1 Γ m n A ->  
  Θ1 ∘ Θ2 => Θ -> eval Θ m Θ' m' ->
  exists Θ1' Θ2' n', 
    well_resolved Θ1' Γ m' n' A /\ 
    pad Θ2 Θ2' /\ Θ1' ∘ Θ2' => Θ' /\ n ~>* n'.
Proof with eauto using 
  clc_type, resolve, resolve_wkU, resolve_wkN, free, pad, merge.
  move=>wf [rm tyn].
  elim: tyn wf Θ1 Θ2 Θ Θ' m m' rm=>{Γ n A}.
  move=>Γ s l k wf Θ1 Θ2 Θ Θ' m m' rsm mrg ev.
  { inv rsm; inv ev.
    exists ((s @ l) :U Θ1).
    exists ((s @ l) :U Θ2).
    exists (s @ l).
    repeat split...
    move:mrg=>/merge_length[<-_].
    repeat split... }
  move=>Γ A B s r t i k tyA ihA tyB ihB wf Θ1 Θ2 Θ Θ' m m' rsm mrg ev.
  { inv rsm; inv ev.
    exists ((Pi A0 B0 s t) :U Θ1).
    exists ((Pi A0 B0 s t) :U Θ2).
    exists (Pi A B s t).
    repeat split...
    move:mrg=>/merge_length[<-_].
    repeat split... }
  move=>Γ x A s hs wf Θ1 Θ2 Θ Θ' m m' rsm mrg ev.
  { inv rsm; inv ev. }
  move=>Γ A B m s t i k tyP ihP tym ihm wf Θ1 Θ2 Θ Θx n m' rsL mrg ev.
  { inv rsL; inv ev.
    have[<-_]:=merge_length mrg.
    destruct t.
    { exists ((Lam A0 m0 s U) :U Θ1).
      exists ((Lam A0 m0 s U) :U Θ2).
      exists (Lam A m s U).
      repeat split... }
    { exists ((Lam A0 m0 s L) :L Θ1).
      exists (_: Θ2).
      exists (Lam A m s L).
      repeat split... } }
  move=>Γ1 Γ2 Γ A B m n s t k mrg1 tym ihm tyn ihn
    wf Θ1 Θ2 Θ Θ' x x' rx mrg2 ev.
  { have[wf1 wf2]:=merge_context_ok_inv mrg1 wf.
    have[r[l tyP]]:= validity wf1 tym.
    have[r0[l0[tyA tyB]]]:= pi_inv _ _ _ _ _ _ tyP.
    inv rx; inv ev.
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have[Θx1[Θx2[mx[wr[pd[mrgx rx]]]]]]:=
        ihm wf1 _ _ _ _ _ _ H4 mrg4 H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      move:wr=>[rx1 tyx].
      exists Θy. exists Θ2p.
      exists (App mx n).
      repeat split...
      econstructor. exact: (merge_sym mrp1).
      exact: rx1. apply: resolve_pad...
      apply: red_app... }
    { have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H1.
      have{ihn}[Θx1[Θx2[nx[wr[pd[mrgx rx]]]]]]:=
        ihn wf2 _ _ _ _ _ _ H5 (merge_sym mrg4) H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      move:wr=>[rx1 tyx].
      exists Θy. exists Θ2p.
      exists (App m nx).
      repeat split...
      econstructor. exact: mrp1.
      apply: resolve_pad... exact: rx1.
      have[e1[e2 e3]]:=merge_re_re mrg1.
      destruct s.
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have mrgs:[Γ1] ∘ Γ2 => Γ2.
        rewrite e1. apply: merge_reL.
        have h:=substitution tyB k mrgs tyn.
        rewrite<-e3.
        rewrite<-pure_re... }
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have h:=substitutionN tyB tyn.
        rewrite e2 in h... }
      apply: red_app... } 
    { move=>{ihm ihn}.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have[G[mrg rs]]:=resolve_free H7 H4 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      exists Gx. exists Θ2. inv rs. exists (m'.[n/]).
      have tym':=lam_inv _ _ _ _ _ _ _ _ _ _ _ tyP tym.
      repeat split...
      admit.
      destruct s; apply: substitution...
      apply: star1.
      apply: step_beta. } }


  (* move=>Γ s l k wf Θ1 Θ2 Θ Θ' m m' A rsm rsA mrg ev.
  { inv rsm; inv ev.
    exists ((s @ l) :U Θ1).
    exists ((s @ l) :U Θ2).
    repeat split...
    move:mrg=>/merge_length[<-_].
    exists (s @ l). exists (U @ l.+1).
    repeat split... }
  move=>Γ A B s r t i k tyA ihA tyB ihB wf Θ1 Θ2 Θ Θ' m m' C
    rsm rsC mrg ev.
  { inv rsm; inv ev.
    exists ((Pi A0 B0 s t) :U Θ1).
    exists ((Pi A0 B0 s t) :U Θ2).
    repeat split...
    move:mrg=>/merge_length[<-_].
    exists (Pi A B s t). exists (t @ i).
    repeat split... }
  move=>Γ x A s hs wf Θ1 Θ2 Θ Θ' m m' C rsm rsC mrg ev.
  { inv rsm; inv ev. }
  move=>Γ A B m s t i k tyP ihP tym ihm wf Θ1 Θ2 Θ Θx n m' C
    rsL rsC mrg ev.
  { inv rsL; inv ev.
    have[<-_]:=merge_length mrg.
    destruct t.
    { exists ((Lam A0 m0 s U) :U Θ1).
      exists ((Lam A0 m0 s U) :U Θ2).
      repeat split...
      exists (Lam A m s U). exists (Pi A B s U).
      repeat split... }
    { exists ((Lam A0 m0 s L) :L Θ1).
      exists (_: Θ2).
      repeat split...
      exists (Lam A m s L). exists (Pi A B s L).
      repeat split... } }
  move=>Γ1 Γ2 Γ A B m n s t k mrg1 tym ihm tyn ihn
    wf Θ1 Θ2 Θ Θ' x x' C rx rC mrg2 ev.
  { have[wf1 wf2]:=merge_context_ok_inv mrg1 wf.
    have[r[l tyP]]:= validity wf1 tym.
    have[r0[l0[tyA tyB]]]:= pi_inv _ _ _ _ _ _ tyP.
    inv rx; inv ev.
    { have rP:=resolve_type_refl Θ0 tyP.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have{ihm}[Θx1[Θx2[wr[pd mrgx]]]]:=
        ihm wf1 _ _ _ _ _ _ _ H4 rP mrg4 H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      exists Θy. exists Θ2p.
      repeat split...
      move:wr=>[mx[tyPx[rx1[rx2 tyx]]]].
      exists (App mx n). exists (B.[n/]).
      repeat split.
      econstructor. exact: (merge_sym mrp1).
      exact: rx1. apply: resolve_pad...
      have[_[<-_]]:=merge_re_re mrp1.
      apply: resolve_pad.
      apply: pad_re...
      have[_[_->]]:=merge_re_re H1...
      have e:=resolve_type_id tyP rx2; subst.
      apply: clc_app... }
    { have rA:=resolve_type_refl Θ3 tyA.
      have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H1.
      have{ihn}[Θx1[Θx2[wr[pd mrgx]]]]:=
        ihn wf2 _ _ _ _ _ _ _ H5 rA (merge_sym mrg4) H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      exists Θy. exists Θ2p.
      repeat split...
      move:wr=>[nx[tyPx[rx1[rx2 tyx]]]].
      exists (App m nx). exists (B.[nx/]).
      repeat split.
      econstructor. exact: mrp1.
      apply: resolve_pad... exact: rx1.
      have[_[<-_]]:=merge_re_re mrp1.
      apply: resolve_pad.
      apply: pad_re...
      have[_[->_]]:=merge_re_re H1...
      have:=eval_red _.
      admit.
      have e:=resolve_type_id tyA rx2; subst.
      apply: clc_app... }

  }
Admitted. *)

Lemma well_resolved_eval Θ Θ' Γ m m' A :
  well_resolved Θ Γ m A -> eval Θ m Θ' m' -> well_resolved Θ' Γ m' A.
Proof with eauto using 
  clc_type, resolve, resolve_wkU, resolve_wkN, free.
  move=>[n[B[rm[rA tyn]]]].
  elim: tyn Θ Θ' m m' A rm rA=>{Γ n B}.
  move=>Γ s l k Θ Θ' m m' A rsm rsA ev.
  { inv rsm. inv ev.
    exists (s @ l). exists (U @ l.+1).
    repeat split...
    inv ev. }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ Θ' m m' C rs1 rs2 ev.
  { inv rs1. inv ev.
    exists (Pi A B s t). exists (t @ i).
    repeat split...
    inv ev. }
  move=>Γ x A s hs Θ Θ' m m' C rs1 rs2 ev.
  { inv rs1. inv ev. inv ev. }
  move=>Γ A B m s t i k tyP ihP tym ihm Θ Θ' rs n C rs1 rs2 ev.
  { inv rs1. inv ev.
    exists (Lam A m s t). exists (Pi A B s t).
    destruct t; repeat split...  
    inv ev. }
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn 
    Θ Θ' n' m' C rs1 rs2 ev.
  { inv rs1. inv ev.
    {
      (* { have[G1[G2[mx[rs'[pd mrg']]]]]:= *)
      have wr:well_resolved Θ1 Γ1 m0 (Pi A B s t).
      exists m. exists (Pi A B s t).
      repeat split...
      admit.
      have[G1[G2[[mx[X[rx1[rx2 tyx]]]][pd mrg']]]]:=eval_split H7 wr H1.
      exists (App mx n). exists (B.[n/]).
      repeat split...
      econstructor...
      exact rx1.

    }
    admit.
    inv ev.

  }

