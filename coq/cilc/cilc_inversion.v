From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma u_Sort_inv Γ s l A :
  [ Γ |- s @ l :- A ] -> U @ l.+1 <: A.
Proof.
  move e:(s @ l)=> n ty. elim: ty s l e=>//={Γ A n}.
  move=> Γ s l p s' l' [_ ->]; eauto.
  move=> Γ A B m s l sb _ _ _ ihM s' l' /ihM sb'.
    apply: sub_trans; eauto.
Qed.

Lemma u_Var_inv Γ x B :
  [ Γ |- Var x :- B ] -> 
  (exists A, hasU Γ x A /\ A <: B) \/
  (exists A, hasL Γ x A /\ A <: B).
Proof.
  move e:(Var x)=> v ty.
  move: Γ v B ty x e.
  apply: has_type_nested_ind; intros; try discriminate.
  - inv e.
    left. exists A; eauto.
  - inv e.
    right. exists A; eauto.
  - subst.
    have e : Var x = Var x by eauto.
    move: (H3 _ e)=>[[A0[hA sb]]|[A0[hA sb]]].
    left. exists A0. firstorder. apply: sub_trans; eauto.
    right. exists A0. firstorder. apply: sub_trans; eauto.
Qed.

Lemma l_Var_inv Γ A B :
  [ A +l Γ |- Var 0 :- B ] -> A.[ren (+1)] <: B.
Proof.
  move e1:(A +l Γ)=> Δ.
  move e2:(Var 0)=> v ty.
  move: Δ v B ty Γ A e1 e2.
  apply: has_type_nested_ind; intros; try discriminate.
  - inv e2.
    inv H; eauto.
  - inv e2.
    inv H; eauto.
  - inv e2.
    apply: sub_trans.
    apply: H3; eauto.
    apply: H.
Qed.

Lemma u_Prod_inv Γ A B C :
  [ Γ |- Prod A B U :- C ] ->
  exists s l l',
    [ Γ |- A :- Sort U l ] /\ 
    [ A +u Γ |- B :- Sort s l ] /\
    Sort U l' <: C.
Proof.
  move e:(Prod A B U)=> n ty. elim: ty A B e =>//={Γ n}.
  move=> Γ A B s l p tyA _ tyB _ A' B' [->->].
    exists s. 
    exists l.
    exists l.
    eauto.
  move=> Γ A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma l_Prod_inv Γ A B C :
  [ Γ |- Prod A B L :- C ] ->
  exists s l l',
    [ Γ |- A :- Sort L l ] /\ 
    [ +n Γ |- B :- Sort s l ] /\
    Sort U l' <: C.
Proof.
  move e:(Prod A B L)=> n ty. elim: ty A B e=>//={Γ n}.
  move=> Γ A B s l p tyA ihA tyB ihB A' B' [->->].
    exists s.
    exists l.
    exists l.
    eauto.
  move=> Γ A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma u_Lolli_inv Γ A B C :
  [ Γ |- Lolli A B U :- C ] ->
  exists s l l',
    [ Γ |- A :- Sort U l ] /\ 
    [ A +u Γ |- B :- Sort s l ] /\
    Sort L l' <: C.
Proof.
  move e:(Lolli A B U)=> n ty. elim: ty A B e=>//={Γ n}.
  move=> Γ A B s l p tyA ihA tyB ihB A' B' [->->].
    exists s.
    exists l.
    exists l.
    eauto.
  move=> Γ A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma l_Lolli_inv Γ A B C :
  [ Γ |- Lolli A B L :- C ] ->
  exists s l l',
    [ Γ |- A :- Sort L l ] /\ 
    [ +n Γ |- B :- Sort s l ] /\
    Sort L l' <: C.
Proof.
  move e:(Lolli A B L)=> n ty. elim: ty A B e=>//={Γ n}.
  move=> Γ A B s l p tyA ihA tyB ihB A' B' [->->].
    exists s.
    exists l.
    eauto.
  move=> Γ A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma u_Lam_invX Γ A0 A1 B C s0 s1 m t l :
  [ Γ |- Lam A0 m s0 :- C ] ->
  (C <: Prod A1 B s1 /\ [ re (A1 +{s1} Γ) |- B :- Sort t l ]) ->
  [ A1 +{s1} Γ |- m :- B ].
Proof.
  move e:(Lam A0 m s0)=> n ty. 
  elim: ty A0 A1 B s0 s1 t l e=>{Γ C n}; intros; try discriminate.
  inv e. inv H4.
    move: (sub_Prod_inv H5)=>[_[sb e]]; subst.
    move: (pure_re H)=> e.
    rewrite e in H0.
    destruct s1.
    move: H0=>/u_Prod_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H5=>/sub_Prod_inv[eA _].
      apply: context_convU.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H2.
    move: H0=>/l_Prod_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H5=>/sub_Prod_inv[eA _].
      apply: context_convL.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H2.
  inv H3. exfalso; solve_sub.
  inv H4.
    apply: H3; eauto.
    split; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma l_Lam_invX Γ A0 A1 B C s0 s1 m t l :
  [ Γ |- Lam A0 m s0 :- C ] ->
  (C <: Lolli A1 B s1 /\ [ re (A1 +{s1} Γ) |- B :- Sort t l ]) ->
  [ A1 +{s1} Γ |- m :- B ].
Proof.
  move e:(Lam A0 m s0)=> n ty.
  elim: ty A0 A1 B s0 s1 t l e=>{Γ C n}; intros; try discriminate.
  inv H4. exfalso; solve_sub.
  inv e. inv H3.
    move: (sub_Lolli_inv H4)=>[_[sb e]]; subst.
    destruct s1.
    move: H=>/u_Lolli_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H4=>/sub_Lolli_inv[eA _].
      apply: context_convU.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H1.
    move: H=>/l_Lolli_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H4=>/sub_Lolli_inv[eA _].
      apply: context_convL.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H1.
  inv H4.
    apply: H3; eauto.
    split; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma u_Lam_inv Γ A0 A1 B s0 s1 m t l :
  [ re Γ |- Prod A1 B s1 :- Sort t l ] ->
  [ Γ |- Lam A0 m s0 :- Prod A1 B s1 ] ->
  [ A1 +{s1} Γ |- m :- B ].
Proof.
  destruct s1.
  move=> /u_Prod_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: u_Lam_invX; eauto.
  move=> /l_Prod_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: u_Lam_invX; eauto.
Qed.

Lemma l_Lam_inv Γ A0 A1 B s0 s1 m t l :
  [ re Γ |- Lolli A1 B s1 :- Sort t l ] ->
  [ Γ |- Lam A0 m s0 :- Lolli A1 B s1 ] ->
  [ A1 +{s1} Γ |- m :- B ].
Proof.
  destruct s1.
  move=> /u_Lolli_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: l_Lam_invX; eauto.
  move=> /l_Lolli_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: l_Lam_invX; eauto.
Qed.

Lemma s_Ind_invX Γ A B Cs s :
  [ Γ |- Ind A Cs s :- B ] ->
  exists t l,
    A <: B /\
    arity s A /\
    List.Forall (constr 0 s) Cs /\
    pure Γ /\
    [ Γ |- A :- Sort U l ] /\
    List.Forall (fun C => [ A +u Γ |- C :- Sort t l ]) Cs.
Proof.
  move e:(Ind A Cs s)=> n ty.
  elim: ty Cs e=>{Γ n}; intros; try discriminate.
  inv e. exists t. exists l. firstorder.
  move: (H3 _ e)=>[t[l'[sb h]]].
    exists t. exists l'. firstorder.
    apply: sub_trans.
    apply: sb.
    apply: H.
Qed.

Lemma s_Ind_inv Γ A Cs s :
  [ Γ |- Ind A Cs s :- A ] ->
  exists t l,
    arity s A /\
    List.Forall (constr 0 s) Cs /\
    pure Γ /\
    [ Γ |- A :- Sort U l ] /\
    List.Forall (fun C => [ A +u Γ |- C :- Sort t l ]) Cs.
Proof. move=> /s_Ind_invX; firstorder. Qed.

Lemma s_Constr_invX Γ i I CI :
  [ Γ |- Constr i I :- CI ] ->
  exists A C Cs s,
    iget i Cs C /\
    pure Γ /\
    I = Ind A Cs s /\
    C.[I/] <: CI /\
    [ Γ |- I :- A ].
Proof.
  move e:(Constr i I)=> n ty.
  elim: ty i I e=>{Γ CI n}; intros; try discriminate.
  - inv e. 
    exists A.
    exists C.
    exists Cs.
    exists s.
    eauto.
  - subst.
    have e : Constr i I = Constr i I by eauto.
    move: (H3 i I e)=>[A0[C[Cs[s0[ig[p[->[sb tyI]]]]]]]].
    exists A0.
    exists C.
    exists Cs.
    exists s0.
    firstorder.
    apply: sub_trans; eauto.
Qed.