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
      have {}tyB := substitutionN n tyB.
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
    have:=substitutionN m' tyB.
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
  { have{}ihA:=ihA _ H4.
    destruct s; simpl in ihA; simpl in tyA.
    have mrg':[Γ2] ∘ Γ1 => [Γ].
    { replace Γ1 with [Γ1].
      apply: merge_re3. apply: merge_sym...
      rewrite<-pure_re... }
    have tyL: [Γ1] ⊢ Left : Either.
    { constructor. apply: re_pure. }
    have tyR: [Γ1] ⊢ Right : Either.
    { constructor. apply: re_pure. }
    have tymA:=substitution tyA k mrg' tym.
    have tymA':=substitution ihA k mrg' tym.
    have tyAL:=substitution ihA (re_pure _) (merge_re3 (merge_sym mrg)) tyL.
    have tyAR:=substitution ihA (re_pure _) (merge_re3 (merge_sym mrg)) tyR.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1i...
    apply: clc_case...
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    rewrite e2...
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    rewrite e2...
    eauto.
    have tymA:=substitutionN m tyA.
    have tymA':=substitutionN m ihA.
    have tyAL:=substitutionN Left ihA.
    have tyAR:=substitutionN Right ihA.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1i...
    apply: clc_case...
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    eauto.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    eauto.
    rewrite<-e2... }
  { have{}ihm:=ihm _ H4.
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
    have tymA:=substitutionN m tyA.
    apply: clc_conv.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_case...
    rewrite<-e2... }
  { have{}ihn1:=ihn1 _ H4.
    apply: clc_case... }
  { have{}ihn2:=ihn2 _ H4.
    apply: clc_case... }
  { have k1:=left_inv tym.
    have->//:=merge_pureL mrg k1. }
  { have k1:=right_inv tym.
    have->//:=merge_pureL mrg k1. }
  move=>Γ1 Γ2 Γ m n A s t k mrg tym ihm tyA ihA tyn ihn n0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. inv st.
  { have[e1[e2 e3]]:=merge_re_re mrg.
    have tyI:[Γ1] ⊢ It : Unit.
    { constructor. apply: re_pure. }
    destruct s; simpl in ihA; simpl in tyA.
    have oA:ok (Unit :U [Γ2]).
    { constructor. apply: re_ok...
      constructor. apply: re_pure... }
    have tyA':=ihA _ oA H3.
    have mrg':[Γ2] ∘ Γ1 => [Γ].
    { replace Γ1 with [Γ1].
      apply: merge_re3. apply: merge_sym...
      rewrite<-pure_re... }
    have tymA:=substitution tyA k mrg' tym.
    have tymA':=substitution tyA' k mrg' tym.
    have tyIA:=substitution tyA' (re_pure _) (merge_re3 (merge_sym mrg)) tyI.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1i...
    apply: clc_letin1...
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    rewrite e3...
    eauto.
    have tyA':=ihA _ (n_ok (re_ok o2)) H3.
    have tymA:=substitutionN m tyA.
    have tymA':=substitutionN m tyA'.
    have tyIA:=substitutionN It tyA'.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1i...
    apply: clc_letin1...
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    eauto.
    rewrite<-e3... }
  { move:(ihm _ o1 H3)=>tym'.
    have[e1[e2 e3]]:=merge_re_re mrg.
    have tyI:[Γ1] ⊢ It : Unit.
    { constructor. apply: re_pure. }
    destruct s; simpl in tyA.
    have mrg':[Γ2] ∘ Γ1 => [Γ].
    { replace Γ1 with [Γ1].
      apply: merge_re3. apply: merge_sym...
      rewrite<-pure_re... }
    have tymA:=substitution tyA k mrg' tym.
    have tymA':=substitution tyA k mrg' tym'.
    apply: clc_conv.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_letin1...
    eauto.
    have tymA:=substitutionN m tyA.
    have tymA':=substitutionN m' tyA.
    apply: clc_conv.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_letin1...
    rewrite<-e3... }
  { move:(ihn _ o2 H3)=>tyn'.
    apply: clc_letin1... }
  { move:(it_inv tym)=>pk.
    by rewrite (merge_pureL mrg pk). }
  move=>Γ1 Γ2 Γ A B C m n s r t k x leq key mrg
    tym ihm tyC ihC tyn ihn n0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2]. 
  move:(validity o1 tym)=>[s0 tyS].
  move:(sigma_inv tyS)=>[G1[G2[_[mrg0[tyA tyB]]]]].
  move:(merge_re_re mrg)=>[e0[e1 e2]].
  move:(merge_re_re mrg0)=>[e3[e4 e5]].
  inv st.
  { destruct k; simpl in tyC; simpl in ihC. inv leq.
    have[D1[D2[leq _]]]:=sigma_inv tyS. inv leq.
    destruct s; destruct r; inv H0.
    have[k1 k2]:=merge_pure_inv mrg0 (re_pure _).
    have[e6 e7]:=merge_pure_eq mrg0 k1 k2.
    have{}tyS:[Γ2] ⊢ Sigma A B U U U : Sort U.
    { rewrite<-e0.
      apply: clc_sigma...
      constructor.
      apply: re_pure.
      rewrite<-e6...
      rewrite<-e7... }
    have oS:ok (Sigma A B U U U :U [Γ2]).
    { constructor. apply: re_ok...
      rewrite<-re_invo... }
    have mrg':[Γ2] ∘ Γ1 => [Γ].
    { replace Γ1 with [Γ1].
      apply: merge_re3. apply: merge_sym...
      rewrite<-pure_re... }
    have tyA':=ihC _ oS H3.
    have tymC:=substitution tyC key mrg' tym.
    have tyP: B :U A :U [Γ2] ⊢ Pair (Var 1) (Var 0) U : (Sigma A B U U U).[ren (+2)].
    { have k0: B :U A :U [Γ2] |> U.
      { repeat constructor. apply: re_pure. }
      have mrg2:B :U A :U [Γ2] ∘ B :U A :U [Γ2] => B :U A :U [Γ2].
      { constructor.
        constructor.
        apply: merge_re_id. }
      apply: clc_pair.
      apply: k0.
      apply: k0.
      apply: mrg2.
      simpl. rewrite<-re_invo.
      have{}tyS:=weakeningU A tyS.
      have{}tyS:=weakeningU B tyS.
      asimpl in tyS.
      asimpl...
      apply: clc_var.
      replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
      econstructor.
      econstructor.
      apply: re_pure.
      apply: clc_var.
      asimpl.
      econstructor.
      constructor.
      apply: re_pure. }
    have tyAx:B :U A :U [Γ2] ⊢ A'.[Pair (Var 1) (Var 0) U .: ren (+2)] : Sort x.
    { have tyAx: (Sigma A B U U U).[ren (+2)] :U B :U A :U [Γ2] ⊢
                   A'.[ren (upren (+2))] : (Sort x).[ren (upren (+2))].
      { apply: rename_ok.
        apply: tyA'.
        constructor.
        constructor.
        constructor.
        apply: agree_ren_refl. }
      replace (Sort x) with (Sort x).[up (ren (+2))].[(Pair (Var 1) (Var 0) U)/] by autosubst.
      replace A'.[Pair (Var 1) (Var 0) U .: ren (+2)]
         with A'.[up (ren (+2))].[(Pair (Var 1) (Var 0) U)/] by autosubst.
      apply: esubstitution.
      asimpl. asimpl in tyAx.
      apply: tyAx.
      constructor.
      apply: agree_subst_refl.
      asimpl.
      rewrite<-re_invo.
      asimpl in tyP... }
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1i...
    apply: clc_letin2.
    constructor.
    apply: key.
    apply: mrg.
    all: eauto.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    eauto.
    eauto.
    have oS:ok (_: [Γ2]).
    { constructor. apply: re_ok... }
    have tyA':=ihC _ oS H3.
    have tymC:=substitutionN m tyC.
    have tyAx: _: [B :{r} A :{s} Γ2] ⊢ A'.[ren (upren (+2))] : (Sort x).[ren (upren (+2))].
    { destruct r; destruct s.
      apply: rename_ok.
      apply: tyA'.
      constructor; simpl.
      constructor.
      constructor.
      apply: agree_ren_refl.
      apply: rename_ok.
      apply: tyA'.
      constructor; simpl.
      constructor.
      constructor.
      apply: agree_ren_refl.
      apply: rename_ok.
      apply: tyA'.
      constructor; simpl.
      constructor.
      constructor.
      apply: agree_ren_refl.
      apply: rename_ok.
      apply: tyA'.
      constructor; simpl.
      constructor.
      constructor.
      apply: agree_ren_refl. }
    have tyP:=substitutionN (Pair (Var 1) (Var 0) t) tyAx.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1i...
    apply: clc_letin2.
    apply: leq.
    apply: key.
    apply: mrg.
    all: eauto.
    apply: clc_conv.
    apply: conv_subst.
    apply: conv1...
    all: eauto.
    asimpl in tyP.
    asimpl...
    rewrite<-e2... }
  { move:(ihm _ o1 H3)=>tym'.
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
    have:=substitutionN m tyC.
    asimpl. by rewrite e2. }
  { rewrite<-re_invo in e4.
    rewrite<-re_invo in e5.
    have[k1 k2]:=merge_pure_inv mrg0 (re_pure _).
    have oAB :ok (B :{r} A :{s} Γ2).
    econstructor.
    econstructor...
    rewrite<-e0. rewrite<-e4. rewrite<-pure_re...
    move:tyB; destruct s=>//=; rewrite e5 e0...
    move:(ihn _ oAB H3)=>tyn'.
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
  move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tym ihm tyn ihn n0 wf st. inv st.
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
