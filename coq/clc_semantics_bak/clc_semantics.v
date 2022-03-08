From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_linearity clc_resolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive eval : context term -> term -> context term -> term -> Prop :=
| eval_sort Θ s i l :
  l = length Θ ->
  eval Θ (Sort s i) (Sort s i :U Θ) (Ptr l)
| eval_pi Θ A B s r t l :
  l = length Θ ->
  eval Θ (Pi A B s r t) (Pi A B s r t :U Θ) (Ptr l)
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

Inductive agree_resolve :
  context term -> context term -> 
    (var -> term) -> (var -> term) -> context term -> Prop :=
| agree_resolve_nil Θ :
  agree_resolve nil Θ ids ids Θ 
| agree_resolve_up Γ Θ Θ' σ σ' A :
  agree_resolve Γ Θ σ σ' Θ' ->
  agree_resolve (A :: Γ) Θ (up σ) (up σ') Θ'
| agree_resolve_wkU Γ Θ Θ1 Θ2 Θ' σ1 σ2 m m' A :
  Θ1 ∘ Θ2 => Θ' ->
  Θ2 |> U ->
  agree_resolve Γ Θ σ1 σ2 Θ1 ->
  resolve Θ2 m m' ->
  agree_resolve (A :U Γ) Θ (m .: σ1) (m' .: σ2) Θ'
| agree_resolve_wkL Γ Θ Θ1 Θ2 Θ' σ1 σ2 m m' A :
  Θ1 ∘ Θ2 => Θ' ->
  agree_resolve Γ Θ σ1 σ2 Θ1 ->
  resolve Θ2 m m' ->
  agree_resolve (A :L Γ) Θ (m .: σ1) (m' .: σ2) Θ'.

Lemma agree_resolve_pure Γ Θ σ σ' Θ' :
  agree_resolve Γ Θ σ σ' Θ' -> Γ |> U -> Θ |> U -> Θ' |> U.
Proof.
  elim=>//{Γ Θ σ σ' Θ'}.
  move=>Γ Θ Θ' σ σ' A agr ih k1 k2. inv k1; eauto.
  move=>Γ Θ Θ1 Θ2 Θ' σ1 σ2 m m' A mrg k1 agr ih rs k2 k3.
    inv k2.
    have k4:=ih H0 k3.
    apply: merge_pure_pure; eauto.
  move=>Γ Θ Θ1 Θ2 Θ' σ1 σ2 m m' A mrg agr ih rs k. inv k.
Qed.

Lemma agree_resolve_free Γ Θ σ σ' Θ' Θ1 l m :
  agree_resolve Γ Θ σ σ' Θ' -> free Θ l m Θ1 -> 
    exists Θ2, free Θ' l m Θ2.
Proof.
  move=>agr. elim: agr l m Θ1=>//{Γ Θ σ σ' Θ'}.
  move=>Θ l m Θ1 fr. exists Θ1; eauto.
  move=>Γ Θ Θ1 Θ2 Θ' σ1 σ2 m m' A mrg k agr ih rs l m0 Θ0 fr.
  { have[Θ3 fr0]:=ih _ _ _ fr.
    have[Θ4 fr1]:=free_merge fr0 mrg.
    exists Θ4. exact: fr1. }
  move=>Γ Θ Θ1 Θ2 Θ' σ1 σ2 m m' A mrg agr ih rs l m0 Θ0 fr.
  { have[Θ3 fr0]:=ih _ _ _ fr.
    have[Θ4 fr1]:=free_merge fr0 mrg.
    exists Θ4. exact: fr1. }
Qed.

Lemma resolve_subst Γ Θ Θ' m m' A r σ σ' :
  Γ ⊢ m' : A : r ->
  resolve Θ m m' -> wr_env Θ ->
  agree_resolve Γ Θ σ σ' Θ' ->
  resolve Θ' m.[σ] m'.[σ'].
Proof.
  move=>ty. elim: ty Θ Θ' m σ σ'=>{Γ m' A r}.
  move=>Γ s l k Θ Θ' m σ σ' rs wr agr.
  { inv rs; simpl.
    constructor.
    apply: agree_resolve_pure; eauto.
    destruct m0; inv H0.
    have e:=free_wr_sort H wr; subst.
    have p:=agree_resolve_pure agr k H3.
    have[Θ2 fr]:=agree_resolve_free agr H.
    have p0:=free_pure fr p.
    econstructor.
    exact: fr.
    constructor; eauto.
    exfalso. apply: free_wr_ptr; eauto. }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ Θ' m σ σ' rs wr agr.
  { destruct m; try solve[inv rs].
    inv rs; simpl.
    constructor.
    apply: agree_resolve_pure; eauto.
    apply: ihA; eauto.
    apply: ihB; eauto.
    destruct s; simpl.
    apply agree_resolve_up.
    rewrite<-pure_re; eauto.
    apply agree_resolve_up.
    rewrite<-pure_re; eauto. 
  }
Admitted.



Lemma resolve_substL Θ1 Θ2 Θ m m' n n' A B r :
  A :L nil ⊢ m' : B : r -> 
  resolve Θ1 m m' -> resolve Θ2 n n' -> wr_env Θ ->
  merge Θ1 Θ2 Θ -> resolve Θ m.[n/] m'.[n'/].
Proof.
  intros.
  apply: resolve_subst.
  apply: H.
  apply: H0.
  admit.
  econstructor.
  apply: H3.
  econstructor.
  apply: H1.


  move e:(A :L nil)=>Γ ty. elim: ty A e Θ1 Θ2 Θ m n n'=>{Γ r m' B};
  intros; subst. 
  { inv H. }
  { inv H. }
  { destruct x. inv H.
    simpl.
    inv H0.
    simpl.
    have->//:=merge_pureL H3 H6.
    have[wr1 wr2]:=wr_merge_inv H3 H2.
    destruct m0; inv H4.
    exfalso.
    apply: free_wr_var.
    apply: H.
    apply: wr1.
    exfalso. apply: free_wr_ptr.
    apply: H.
    apply: wr1.
    inv H. }
  { inv H.
    destruct m0; inv H4.
    admit.
    asimpl.
    asimpl.
    econstructor.

  }
  admit. *)
  
  

Lemma eval_split Θ1 Θ2 Θ Θ' m n m' A t :
  well_resolved Θ1 m n A t -> wr_env Θ -> 
  Θ1 ∘ Θ2 => Θ -> eval Θ m Θ' m' ->
  exists Θ1' Θ2' n', 
    well_resolved Θ1' m' n' A t /\ wr_env Θ' /\
    pad Θ2 Θ2' /\ Θ1' ∘ Θ2' => Θ' /\ n ~>* n'.
Proof with eauto 6 using 
  clc_type, key, free, pad, merge, 
  well_resolved, resolve, resolve_wkU, resolve_wkN.
  move=>{Θ1 m n A t}[Θ1 m n A t rm]. move e:(nil)=>Γ tyn.
  elim: tyn Θ1 Θ2 Θ Θ' m m' rm e=>{Γ n A t}.
  move=>Γ s l k Θ1 Θ2 Θ Θ' m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev.
    exists ((s @ l) :U Θ1).
    exists ((s @ l) :U Θ2).
    exists (s @ l).
    repeat split...
    econstructor.
    move:mrg=>/merge_length[<-_]... 
    econstructor... 
    econstructor... }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ1 Θ2 Θ Θ' 
    m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    exists ((Pi A0 B0 s r t) :U Θ1).
    exists ((Pi A0 B0 s r t) :U Θ2).
    exists (Pi A B s r t).
    repeat split...
    econstructor.
    move:mrg=>/merge_length[<-_]... 
    econstructor... 
    econstructor... 
    have//=nfA:=nf_typing tyA.
    have//:=resolve_wr_nfi H7 wr1 nfA.
    destruct s; simpl in tyB.
    have//=nfB:=nf_typing tyB.
    have//:=resolve_wr_nfi H8 wr1 nfB.
    have//=nfB:=nf_typing tyB.
    have//:=resolve_wr_nfi H8 wr1 nfB. }
  move=>Γ x A s hs Θ1 Θ2 Θ Θ' m m' rsm e tyA mrg ev.
  { inv rsm; inv ev. }
  move=>Γ A B m s r t i k tyP ihP tym ihm 
    Θ1 Θ2 Θ Θx n m' rsL e wr mrg ev.
  { inv rsL; inv ev.
    have[<-_]:=merge_length mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct t.
    { exists ((Lam A0 m0 s U) :U Θ1).
      exists ((Lam A0 m0 s U) :U Θ2).
      exists (Lam A m s U).
      repeat split... 
      econstructor... 
      have[l0[tyA[_ _]]]:=pi_inv _ _ _ _ _ _ _ _ tyP.
      have//=nfA:=nf_typing tyA.
      have//:=resolve_wr_nfi H6 (wr_env_re wr1) nfA.
      destruct s.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm. }
    { exists ((Lam A0 m0 s L) :L Θ1).
      exists (_: Θ2).
      exists (Lam A m s L).
      repeat split... 
      econstructor... 
      have[l0[tyA[_ _]]]:=pi_inv _ _ _ _ _ _ _ _ tyP.
      have//=nfA:=nf_typing tyA.
      have//:=resolve_wr_nfi H6 (wr_env_re wr1) nfA.
      destruct s.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm. } }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg1 tym ihm tyn ihn
    Θ1 Θ2 Θ Θ' x x' rx e wf mrg2 ev; subst.
  { inv mrg1.
    have[l tyP]:= validity nil_ok tym.
    have[l0[tyA[_ tyB]]]:= pi_inv _ _ _ _ _ _ _ _ tyP.
    inv rx; inv ev.
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have[Θx1[Θx2[mx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihm _ _ _ _ _ _ H4 erefl wf mrg4 H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App mx n).
      repeat split...
      econstructor.
      exact: (merge_sym mrp1).
      eauto.
      apply: resolve_pad...
      apply: red_app... }
    { have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H1.
      have{ihn}[Θx1[Θx2[nx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihn _ _ _ _ _ _ H5 erefl wf (merge_sym mrg4) H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App m nx).
      repeat split...
      econstructor. 
      exact: mrp1.
      apply: resolve_pad... eauto.
      destruct s.
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have mrgs:[@nil (elem term)] ∘ nil => nil. simpl...
        have h:=substitution tyB k mrgs tyn... }
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have h:=substitutionN tyB tyn... }
      eauto.
      apply: red_app... } 
    { move=>{ihm ihn}.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have[G[mrg rs]]:=resolve_free H7 H4 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      exists Gx. exists Θ2. inv rs. exists (m'.[n/]).
      have tym':=lam_inv _ _ _ _ _ _ _ _ _ _ _ _ _ tyP tym.
      repeat split...
      have[wf1 wf2]:=wr_merge_inv mrg2 wf.
      have[wf0 wf3]:=wr_merge_inv H1 wf1.
      have vn:=wr_resolve_value wf3 H5.
      have key:=resolution tyn vn wf3 H5.
      destruct s.
      { admit. }
      { have os:of_sort (A :L nil) 0 (Some L) by constructor.
        have {}os:=linearity tym' os.

      }
      

      admit.
      apply: substitution...
      apply: free_wr...
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

