From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution.

Ltac solve_sub :=
  match goal with
  | [ H : _ <: _ |- _ ] =>
    let A := fresh "A" in
    let B := fresh "B" in
    let sb := fresh "sb" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    destruct H as [A B sb c1 c2]; destruct sb
  end;
  match goal with
  | [ c1 : ?A === ?x, c2 : ?x === ?B |- _ ] => 
    assert (A === B) by 
      (eapply conv_trans; try solve [apply c1| apply c2]);
    clear c1 c2;
    solve_conv
  | _ => solve_conv
  end.

Lemma pi_inv Γ A B C s t :
  Γ ⊢ Pi A B s t : C ->
  exists r l,
    Γ ⊢ A : s @ l /\ 
    match s with U => A :U Γ | L => _: Γ end ⊢ B : r @ l.
Proof with eauto using key.
  move e:(Pi A B s t)=>m tp.
  elim: tp A B s t e=>//{Γ C m}.
  move=>Γ A B s r t i k tyA ihA tyB ihB A0 B0 s0 t0[->->e _]; subst.
  exists r. exists i.
  split; eauto.
  destruct s.
  simpl in tyB. rewrite<-pure_re in tyB...
  simpl in tyB. rewrite<-pure_re in tyB...
Qed.

Lemma lam_invX Γ A1 A2 B C m s1 s2 t1 t2 r l :
  Γ ⊢ Lam A1 m s1 t1 : C ->
  C <: Pi A2 B s2 t2 ->
  [A2 :{s2} Γ] ⊢ B : r @ l ->
  A2 :{s2} Γ ⊢ m : B.
Proof.
  move e:(Lam A1 m s1 t1)=>n tpL.
  elim: tpL A1 A2 B m s1 t1 s2 t2 r l e=>//{Γ C n}.
  move=>Γ A B m s r t i k tyP ih tym ihm A1 A2 B0 m0
    s1 t1 s2 t2 r0 l[e1 e2 e3 e4]/sub_pi_inv[c[sbB[e5 e6]]] tyB0; subst.
  { move:tyP=>/pi_inv[r1[l0[tyA tyB]]].
    destruct s2.
    apply: clc_conv; eauto.
    apply: context_conv.
    apply: conv_sym; eauto.
    eauto.
    eauto.
    apply: clc_conv; eauto.
    apply: context_conv.
    apply: conv_sym; eauto.
    eauto.
    eauto. }
  move=>Γ A B m s i sb1 tym ihm tyB ihB A1 A2 B0 m0 
    s1 t1 s2 t2 r l e sb2 tyB0; subst.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma lam_inv Γ m A1 A2 B s1 s2 t1 t2 r l :
  [Γ] ⊢ Pi A1 B s1 t1 : r @ l ->
  Γ ⊢ Lam A2 m s2 t2 : Pi A1 B s1 t1 ->
  A1 :{s1} Γ ⊢ m : B.
Proof.
  move=> /pi_inv[t[i[tyA tyB]]] tyL.
  apply: lam_invX; eauto.
Qed.