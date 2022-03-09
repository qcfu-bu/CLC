From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem subject_step Γ m n A s :
  ok Γ -> Γ ⊢ m : A : s -> m ~> n -> Γ ⊢ n : A : s.
Proof with eauto using clc_type, step, ok, merge_re_id.
  move=>wf tp. elim: tp n wf=>{Γ m A s}.
  move=>Γ s l k n o st. inv st.
  move=>Γ A B s r t i k tyA ihA tyB ihB n o st. inv st.
  { move:(ihA _ o H5)=>tyA'.
    apply: clc_pi...
    destruct s=>//=.
    apply: context_conv.
    apply: conv_sym.
    apply: conv1...
    rewrite<-re_invo.
    rewrite<-pure_re...
    exact: tyB. }
  { destruct s.
    have /ihB{}ihB :(ok [A :U Γ]).
      simpl.
      apply: ty_ok.
      apply: re_ok...
      rewrite<-re_invo.
      rewrite<-pure_re...
    move:(ihB _ H5)=>tyB'.
    apply: clc_pi...
    have /ihB{}ihB :(ok [A :L Γ]).
      simpl.
      apply: n_ok.
      apply: re_ok...
    move:(ihB _ H5)=>tyB'.
    apply: clc_pi... }
  move=>Γ x A s hs n o st. inv st.
  move=>Γ A B m s r t i k tyP ihP tym ihm n o st.
  move:(pi_inv _ _ _ _ _ _ _ _ tyP)=>[l[tyA[_ tyB]]]. inv st.
  { have: ok (A :{s} Γ)... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn m0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2].
  move:(ihm^~ o1)=>{}ihm.
  move:(ihn^~ o2)=>{}ihn. 
  move:(validity o1 tym)=>[lP tyP]. inv st.
  { move:(lam_inv _ _ _ _ _ _ _ _ _ _ _ _ tyP tym)=>tym1.
    apply: substitution... }
  { move:(ihm _ H2)=>{}ihm.
    apply: clc_app... }
  { move:(ihn _ H2)=>{}ihn.
    move:(pi_inv _ _ _ _ _ _ _ _ tyP)=>[l[tyA[_ tyB]]].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    destruct s.
    { have mrg' : [Γ1] ∘ Γ2 => [Γ].
        replace Γ2 with [Γ2].
        rewrite e2 e3...
        rewrite<-pure_re...
      have {}tyB := substitution tyB k mrg' tyn.
      apply: clc_conv.
      apply: conv_sub.
      apply: conv_beta.
      apply: conv1i...
      apply: clc_app...
      exact: tyB. }
    { have {}tyB := substitutionN tyB tyn.
      apply: clc_conv.
      apply: conv_sub.
      apply: conv_beta.
      apply: conv1i...
      apply: clc_app...
      rewrite<-e2.
      exact: tyB. } }
  move=>Γ k n o st. inv st.
  move=>Γ k n o st. inv st.
  move=>Γ A B s r t i mrg k tyA ihA tyB ihB n o st. inv st.
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
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg
    tyS ihS tym ihm tyn ihn n0 o st. 
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. 
  move:(merge_re_re mrg)=>[e[e1 e2]].
  move:(sigma_inv _ _ _ _ _ _ _ tyS)=>[G1[G2[i0[mrg0[tyA tyB]]]]].
  move:(merge_re_re mrg0)=>[e3[e4 e5]]. inv st.
  { move:(ihm _ o1 H3)=>{ihm ihS ihn}tym'.
    rewrite<-re_invo in e4.
    rewrite<-re_invo in e5.
    apply:clc_pair...
    apply:clc_conv.
    apply:conv_sub.
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
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn ihn n0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. inv st.
  { move:(ihm _ o1 H2)=>tym'.
    apply: clc_letin1... }
  { move:(ihn _ o2 H2)=>tyn'.
    apply: clc_letin1... }
  { move:(it_inv _ _ tym)=>k.
    by rewrite (merge_pureL mrg k). }
  move=>Γ1 Γ2 Γ A B C m n s r t k x i leq key mrg 
    tym ihm tyC ihC tyn ihn n0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. 
  move:(validity o1 tym)=>[l tyS].
  move:(sigma_inv _ _ _ _ _ _ _ tyS)=>[G1[G2[i0[mrg0[tyA tyB]]]]]. 
  move:(merge_re_re mrg)=>[e0[e1 e2]].
  move:(merge_re_re mrg0)=>[e3[e4 e5]].
  inv st.
  { move:(ihm _ o1 H2)=>tym'.
    apply: clc_conv.
    apply: conv_sub.
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
    move:(pair_inv _ _ _ _ _ _ _ _ _ _ _ _ tym tyS)=>
      [G3[G4[->[et[k1[k2[mrg1[tym1 tym2]]]]]]]]; subst.
    have[G[/merge_sym mrg2 /merge_sym mrg3]]:=merge_splitL mrg mrg1.
    have:=substitution2 tyn k1 k2 mrg2 mrg3 tym1 tym2.
    by asimpl. }
  move=>Γ A B m s i sb tym ihm tyB ihB n o st.
  { apply: clc_conv... }
Qed.

Theorem subject_reduction Γ m n A s :
  ok Γ -> Γ ⊢ m : A : s -> m ~>* n -> Γ ⊢ n : A : s.
Proof.
  move=>wf tym rd. elim: rd; eauto.
  move=>y z rd ih st.
  apply: subject_step.
  exact: wf.
  exact: ih.
  exact: st.
Qed.