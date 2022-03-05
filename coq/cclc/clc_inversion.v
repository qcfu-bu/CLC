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
  move=>Γ A B m s t i k tyP ih tym ihm A1 A2 B0 m0
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

Lemma it_invX Γ1 A :
  Γ1 ⊢ It : A -> A <: Unit -> Γ1 |> U.
Proof.
  move e:(It)=>m tp. elim:tp e=>//{Γ1 m A}.
  move=>Γ A B m s i sb1 tym ihm tyB ihB e sb2; subst.
  apply: ihm; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma it_inv Γ1 : Γ1 ⊢ It : Unit -> Γ1 |> U.
Proof. move=>ty. apply: it_invX; eauto. Qed.

Lemma sigma_inv Γ A B s r t x :
  Γ ⊢ Sigma A B s r t : x ->
  exists Γ1 Γ2 i,
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ A : s @ i /\ [A :{s} Γ2] ⊢ B : r @ i.
Proof.
  move e:(Sigma A B s r t)=>m ty. 
  elim: ty A B s r t e=>//{Γ x m}.
  move=>Γ A B s r t i mrg k 
    tyA ihA tyB ihB A0 B0 s0 r0 t0 [e1 e2 e3 e4 e5]; subst.
  exists Γ. exists Γ. 
  exists i. firstorder.
  by apply: merge_pure.
Qed.

Lemma pair_invX Γ m n t1 C :
  Γ ⊢ Pair m n t1 : C ->
  forall A B s r t2 x l,
    C <: Sigma A B s r t2 ->
    [Γ] ⊢ Sigma A B s r t2 : x @ l ->
    exists Γ1 Γ2,
      t1 = t2 /\
      Γ1 |> s /\ 
      Γ2 |> r /\
      Γ1 ∘ Γ2 => Γ /\
      Γ1 ⊢ m : A /\ Γ2 ⊢ n : B.[m/].
Proof.
  move e:(Pair m n t1)=>v tp. elim: tp m n t1 e=>//{Γ v C}.
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg.
  move=>/sigma_inv[G1[G2[i0[mrg0[tyA tyB]]]]].
  move=>_ tym _ tyn _ m0 n0 t1 [e1 e2] e3 A0 B0 s1 r1 t2 x l.
  move=>/sub_sigma_inv[sbA[sbB[e4[e5 e6]]]]; subst.
  move=>/sigma_inv[G3[G4[i1[mrg1[tyA0 tyB0]]]]].
  { exists Γ1. exists Γ2.
    have[_[e1 e2]]:=merge_re_re mrg.
    have[_[e3 e4]]:=merge_re_re mrg1.
    rewrite<-re_invo in e3.
    rewrite<-re_invo in e4.
    have[k3 k4]:=merge_pure_inv mrg1 (re_pure _).
    repeat split; eauto.
    apply: clc_conv; eauto.
    rewrite e1.
    rewrite<-e3.
    rewrite<-pure_re; eauto.
    apply: clc_conv.
    apply: sub_subst; eauto.
    eauto.
    destruct s1; simpl in tyB0.
    { have mrg2:[G4] ∘ Γ1 => [Γ2].
      rewrite e4 e2 (pure_re k1) e1.
      apply: merge_re_id.
      have {}tym:Γ1 ⊢ m : A0.
      apply:clc_conv; eauto.
      rewrite e1. rewrite<-e3. rewrite<-pure_re; eauto.
      have:=substitution tyB0 k1 mrg2 tym. 
      asimpl; eauto. }
    { have:=substitutionN tyB0 tym.
      rewrite e4. by rewrite<-e2. } }
  move=>Γ A B m s i sb1 tym ihm tyB ihB 
    m0 n e A0 B0 s0 r t x l sb2 tyS; subst.
  { apply: ihm; eauto.
    apply: sub_trans; eauto. }
Qed.

Lemma pair_inv Γ m n A B s r t1 t2 x i :
  Γ ⊢ Pair m n t1 : Sigma A B s r t2 ->
  [Γ] ⊢ Sigma A B s r t2 : x @ i ->
  exists Γ1 Γ2,
    t1 = t2 /\
    Γ1 |> s /\ 
    Γ2 |> r /\
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : A /\ Γ2 ⊢ n : B.[m/].
Proof. move=>tyP tyS. apply: pair_invX; eauto. Qed.