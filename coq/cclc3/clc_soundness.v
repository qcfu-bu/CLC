From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Export clc_validity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem subject_step Γ m n A :
  ok Γ -> Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using clc_type, step, ok, merge_re_id.
  move=>wf tp. elim: tp n wf=>{Γ m A}.
  move=>Γ s k n o st. inv st.
  move=>Γ A B s r t k tyA ihA tyB ihB n o st. inv st.
  { move:(ihA _ o H4)=>tyA'.
    apply: clc_pi...
    destruct s=>//=.
    apply: context_conv.
    apply: conv_sym.
    apply: conv1...
    rewrite<-re_invo.
    rewrite<-pure_re...
    exact: tyB.
    eauto. }
  { destruct s.
    have /ihB{}ihB :(ok [A :U Γ]).
      simpl.
      apply: ty_ok.
      apply: re_ok...
      rewrite<-re_invo.
      rewrite<-pure_re...
    move:(ihB _ H4)=>tyB'.
    apply: clc_pi...
    have /ihB{}ihB :(ok [A :L Γ]).
      simpl.
      apply: n_ok.
      apply: re_ok...
    move:(ihB _ H4)=>tyB'.
    apply: clc_pi... }
  move=>Γ x A s hs n o st. inv st.
  move=>Γ A B m s t k tyP ihP tym ihm n o st.
  move:(pi_inv tyP)=>[tyA[r tyB]]. inv st.
  { have st : Pi A B s t ~> Pi A' B s t...
    move:(ihP _ (re_ok o) st)=>tyP'.
    apply: clc_conv.
    apply: conv1i...
    apply: clc_lam...
    apply: context_conv.
    apply: conv1i...
    exact: tyA.
    exact: tym.
    exact: tyP. }
  { have: ok (A :{s} Γ)... }
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn m0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2].
  move:(ihm^~ o1)=>{}ihm.
  move:(ihn^~ o2)=>{}ihn. 
  move:(validity o1 tym)=>[s0 tyP]. inv st.
  { move:(lam_inv tyP tym)=>tym1.
    apply: substitution... }
  { move:(ihm _ H2)=>{}ihm.
    apply: clc_app... }
  { move:(ihn _ H2)=>{}ihn.
    move:(pi_inv tyP)=>[tyA[r tyB]].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    destruct s.
    { have mrg' : [Γ1] ∘ Γ2 => [Γ].
        replace Γ2 with [Γ2].
        rewrite e2 e3...
        rewrite<-pure_re...
      simpl in tyB. rewrite<-re_invo in tyB.
      have {}tyB := substitution tyB k mrg' tyn.
      apply: clc_conv.
      apply: conv_beta.
      apply: conv1i...
      apply: clc_app...
      exact: tyB. }
    { simpl in tyB. rewrite<-re_invo in tyB.
      have {}tyB := substitutionN tyB tyn.
      apply: clc_conv.
      apply: conv_beta.
      apply: conv1i...
      apply: clc_app...
      rewrite<-e2.
      exact: tyB. } }
  move=>Γ A m k tyA ihA tym ihm n o st. inv st.
  { have tyA':=ihA _ o H2.
    apply: clc_conv.
    apply: conv1i...
    apply: clc_fix...
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    apply: context_conv.
    apply: conv1i...
    rewrite<-pure_re...
    eauto.
    simpl.
    replace (Sort U) with (Sort U).[ren (+1)] by eauto.
    apply: eweakeningU...
    rewrite<-pure_re...
    rewrite<-pure_re... }
  { have wf: ok (A :U Γ).
    { constructor...
      rewrite<-pure_re... }
    have tym':=ihm _ wf H2.
    constructor... }
  { have tyF : Γ ⊢ Fix A m : A.
    { constructor... }
    have:=substitution tym k (merge_pure k) tyF.
    asimpl... }
  move=>Γ k n o st. inv st.
  move=>Γ k n o st. inv st.
  move=>Γ k n o st. inv st.
  move=>Γ k n o st. inv st.
  move=>Γ k n o st. inv st.
  move=>Γ A B s r t mrg k tyA ihA tyB ihB n o st. inv st.
  { move:(ihA _ o H5)=>{ihA}tyA'.
    apply: clc_sigma...
    destruct s; simpl.
    apply: context_conv.
    apply: conv1i...
    rewrite<-re_invo.
    rewrite<-pure_re...
    exact: tyB.
    exact: tyB. }
  { destruct s; simpl in tyB.
    have okA:ok (A :U [Γ]).
    apply: ty_ok...
    rewrite<-pure_re...
    rewrite<-re_invo.
    rewrite<-pure_re...
    move:(ihB _ okA H5)=>//=tyB'.
    apply: clc_sigma...
    move:(ihB _ (n_ok (re_ok o)) H5)=>//=tyB'.
    apply: clc_sigma... }
  move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg
    tyS ihS tym ihm tyn ihn n0 o st. 
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. 
  move:(merge_re_re mrg)=>[e[e1 e2]].
  move:(sigma_inv tyS)=>[G1[G2[_[mrg0[tyA tyB]]]]].
  move:(merge_re_re mrg0)=>[e3[e4 e5]]. inv st.
  { move:(ihm _ o1 H3)=>{ihm ihS ihn}tym'.
    rewrite<-re_invo in e4.
    rewrite<-re_invo in e5.
    apply:clc_pair...
    apply:clc_conv.
    apply:conv_beta.
    apply:conv1...
    exact:tyn.
    destruct s; simpl in tyB.
    have mrg1:[G2] ∘ Γ1 => [Γ2].
    rewrite e5 e2 (pure_re k1) e1.
    apply:merge_re_id.
    have:=substitution tyB k1 mrg1 tym'. asimpl...
    have:=substitutionN tyB tym'. 
    rewrite e5. rewrite<-e2... }
  { move:(ihn _ o2 H3)=>{ihm ihS ihn}tyn'.
    apply:clc_pair... }
  move=>Γ1 Γ2 Γ m n1 n2 A s t k mrg
    tym ihm tyA ihA tyn1 ihn1 tyn2 ihn2 n wf st.
  have[wf1 wf2]:=merge_context_ok_inv mrg wf.
  have{}ihm:=ihm _ wf1.
  have{}ihn1:=ihn1 _ wf2.
  have{}ihn2:=ihn2 _ wf2.
  have/ihA{}ihA:ok [Either :{s} Γ2].
  { destruct s; simpl.
    econstructor.
    apply: re_ok...
    apply: clc_either.
    apply: re_pure.
    constructor.
    apply: re_ok... }
  have[_[e1 e2]]:=merge_re_re mrg.
  inv st.
  { have{}ihm:=ihm _ H3.
    destruct s; simpl in tyA.
    have mrg':[Γ2] ∘ Γ1 => [Γ].
    { replace Γ1 with [Γ1].
      apply: merge_re3. apply: merge_sym...
      rewrite<-pure_re... }
    have tymA:=substitution tyA k mrg' tym.
    apply: clc_conv.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_case...
    apply: tymA.
    have tymA:=substitutionN tyA tym.
    apply: clc_conv.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_case...
    rewrite<-e2... }
  { have{}ihn1:=ihn1 _ H3.
    apply: clc_case... }
  { have{}ihn2:=ihn2 _ H3.
    apply: clc_case... }
  { have k1:=left_inv tym.
    have->//:=merge_pureL mrg k1. }
  { have k1:=right_inv tym.
    have->//:=merge_pureL mrg k1. }
  move=>Γ1 Γ2 Γ m n A mrg tym ihm tyn ihn n0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. inv st.
  { move:(ihm _ o1 H2)=>tym'.
    apply: clc_letin1... }
  { move:(ihn _ o2 H2)=>tyn'.
    apply: clc_letin1... }
  { move:(it_inv tym)=>k.
    by rewrite (merge_pureL mrg k). }
  move=>Γ1 Γ2 Γ A B C m n s r t k x leq key mrg
    tym ihm tyC ihC tyn ihn n0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. 
  move:(validity o1 tym)=>[s0 tyS].
  move:(sigma_inv tyS)=>[G1[G2[_[mrg0[tyA tyB]]]]].
  move:(merge_re_re mrg)=>[e0[e1 e2]].
  move:(merge_re_re mrg0)=>[e3[e4 e5]].
  inv st.
  { move:(ihm _ o1 H2)=>tym'.
    apply: clc_conv.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_letin2...
    destruct k; simpl in tyC.
    have mrg1:[Γ2] ∘ Γ1 => [Γ].
    rewrite e2 (pure_re key) e1.
    apply:merge_re_id. inv leq.
    have:=substitution tyC key mrg1 tym.
    asimpl...
    have:=substitutionN tyC tym.
    asimpl. by rewrite e2. }
  { rewrite<-re_invo in e4.
    rewrite<-re_invo in e5.
    have[k1 k2]:=merge_pure_inv mrg0 (re_pure _).
    have oAB :ok (B :{r} A :{s} Γ2).
    econstructor.
    econstructor...
    rewrite<-e0. rewrite<-e4. rewrite<-pure_re...
    move:tyB; destruct s=>//=; rewrite e5 e0...
    move:(ihn _ oAB H2)=>tyn'.
    apply: clc_letin2... }
  { rewrite<-re_invo in e4.
    rewrite<-re_invo in e5.
    move:(pair_inv tym tyS)=>
      [G3[G4[->[k1[k2[mrg1[tym1 tym2]]]]]]]; subst.
    have[G[/merge_sym mrg2 /merge_sym mrg3]]:=merge_splitL mrg mrg1.
    have:=substitution2 tyn k1 k2 mrg2 mrg3 tym1 tym2.
    by asimpl. }
  move=>Γ k n wf st. inv st.
  move=>Γ k n o st. inv st.
  move=>Γ r k n o st. inv st.
  move=>Γ r A B s k tyA ihA tyB ihB n o st. inv st.
  { constructor...
    destruct s; simpl...
    apply: context_conv.
    apply: conv1i...
    rewrite<-re_invo.
    rewrite<-pure_re...
    exact: tyB. }
  { constructor...
    apply: ihB...
    destruct s; simpl.
    econstructor.
    apply: re_ok...
    rewrite<-re_invo.
    rewrite<-pure_re...
    econstructor.
    apply: re_ok... }
  move=>Γ r A k tyA ihA n o st. inv st.
  { constructor... }
  move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tyA ihA tym ihm tyn ihn n0 wf st. inv st.
  { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
    econstructor... }
  { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
    econstructor... }
  move=>Γ r1 r2 A B m s xor tym ihm n o st. inv st.
  { econstructor... }
  move=>Γ r1 r2 A B m s xor tym ihm n o st. inv st.
  { econstructor... }
  move=>Γ r1 r2 m xor tym ihm n o st. inv st.
  { econstructor... }
  move=>Γ r1 r2 m xor tym ihm n o st. inv st.
  { econstructor... }
  move=>Γ A B m s sb tym ihm tyB ihB n o st.
  { apply: clc_conv... }
Qed.

Theorem subject_reduction Γ m n A :
  ok Γ -> Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof.
  move=>wf tym rd. elim: rd; eauto.
  move=>y z rd ih st.
  apply: subject_step.
  exact: wf.
  exact: ih.
  exact: st.
Qed.
