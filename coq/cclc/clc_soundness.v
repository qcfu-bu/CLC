From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem subject_reduction Γ m n A :
  ok Γ -> Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using clc_type, step, ok, merge_re_id.
  move=>wf tp. elim: tp n wf=>{Γ m A}.
  move=>Γ s l k n o st. inv st.
  move=>Γ A B s r t i k tyA ihA tyB ihB n o st. inv st.
  { move:(ihA _ o H4)=>tyA'.
    apply: clc_pi...
    destruct s=>//=.
    apply: context_conv.
    apply: conv_sym.
    apply: conv1...
    rewrite<-re_invo.
    rewrite<-pure_re...
    exact: tyB.
    exact: tyB. }
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
  move=>Γ A B m s t i k tyP ihP tym ihm n o st. inv st.
  { have st : Pi A B s t ~> Pi A' B s t...
    move:(pi_inv _ _ _ _ _ _ tyP)=>[r0[l[tyA tyB]]].
    move:(ihP _ (re_ok o) st)=>tyP'.
    apply: clc_conv.
    apply: conv_sub.
    apply: conv1i...
    apply: clc_lam...
    apply: context_conv.
    apply: conv1i...
    exact: tyA.
    exact: tym.
    exact: tyP. }
  { move:(pi_inv _ _ _ _ _ _ tyP)=>[r0[l[tyA tyB]]].
    have: ok (A :{s} Γ)... }
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn m0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2].
  move:(ihm^~ o1)=>{}ihm.
  move:(ihn^~ o2)=>{}ihn. inv st.
  { move:(validity o1 tym)=>[sP[lP tyP]].
    move:(lam_inv _ _ _ _ _ _ _ _ _ _ _ tyP tym)=>tym1.
    apply: substitution... }
  { move:(ihm _ H2)=>{}ihm.
    apply: clc_app... }
  { move:(ihn _ H2)=>{}ihn.
    move:(validity o1 tym)=>[sP[lP tyP]].
    move:(pi_inv _ _ _ _ _ _ tyP)=>[r[l[tyA tyB]]].
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
  move=>Γ A B m s i sb tym ihm tyB ihB n o st.
  { apply: clc_conv... }
Qed.