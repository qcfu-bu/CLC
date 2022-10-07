From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Export clc_soundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma clc_sort_uniq Γ s A :
  Γ ⊢ Sort s : A -> Sort U === A.
Proof with eauto.
  move e:(Sort s)=>n ty. elim: ty s e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB t e; subst.
  apply: conv_trans.
  apply: ihm...
  exact: eq.
Qed.

Lemma clc_pi_uniq Γ A B s t C :
  Γ ⊢ Pi A B s t : C -> Sort t === C.
Proof with eauto.
  move e:(Pi A B s t)=>n ty. elim: ty A B s t e=>//{Γ n C}.
  move=>Γ A B s r t k tyA ihA tyB ihB A0 B0 s0 t0[e1 e2 e3->]//.
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 t e; subst.
  apply: conv_trans.
  apply: ihm...
  exact: eq.
Qed.

Lemma clc_has_subset Γ Γ1 Γ2 G1 G2 A B x s t :
  has Γ1 x s A -> has Γ2 x t B -> Γ1 ∘ G1 => Γ -> Γ2 ∘ G2 => Γ -> A = B /\ s = t.
Proof with eauto.
  move=>hs. elim: hs Γ Γ2 G1 G2 B t=>{Γ1 x s A}.
  move=>Γ A s k Γ0 Γ2 G1 G2 B t hs mrg1 mrg2.
  { inv mrg1; inv mrg2; inv hs... }
  move=>Γ A B x s hs1 ih Γ0 Γ2 G1 G2 B0 t hs2 mrg1 mrg2.
  { inv mrg1. inv mrg2. inv hs2.
    have[->->//]:=ih _ _ _ _ _ _ H6 H3 H2. }
  move=>Γ A x s hs1 ih Γ0 Γ2 G1 G2 B t hs2 mrg1 mrg2.
  { inv mrg1. inv mrg2; inv hs2.
    have[->->//]:=ih _ _ _ _ _ _ H2 H0 H3.
    inv mrg2. inv hs2.
    have[->->//]:=ih _ _ _ _ _ _ H2 H0 H3. }
Qed.
    
Lemma clc_has_uniq Γ A B x s t : has Γ x s A -> has Γ x t B -> A = B.
Proof with eauto.
  move=>hs. elim: hs B t=>{Γ x s A}.
  move=>Γ A s k B t hs. inv hs...
  move=>Γ A B x s hs1 ih B0 t hs2.
  { inv hs2. rewrite (ih _ _ H4)... }
  move=>Γ A x s hs1 ih B t hs2.
  { inv hs2. rewrite (ih _ _ H1)... }
Qed.

Lemma clc_var_uniq Γ A B x s :
  Γ ⊢ Var x : B -> has Γ x s A -> A === B.
Proof with eauto.
  move e:(Var x)=>n ty. elim: ty A x s e=>//{Γ n B}.
  move=>Γ x A s hs1 A0 x0 s0[e]hs2; subst.
  { rewrite (clc_has_uniq hs1 hs2)... }
  move=>Γ A B m s eq tym ihm tyB ihB A0 x s0 e hs; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_lam_uniq Γ A B C m s t :
  Γ ⊢ Lam A m s t : C -> (forall C, A :{s} Γ ⊢ m : C -> B === C) -> Pi A B s t === C.
Proof with eauto.
  move e:(Lam A m s t)=>n ty. elim: ty A B m s t e=>//{Γ n C}.
  move=>Γ A B m s t k tyP ihP tym ihm A0 B0 m0 s0 t0[e1 e2 e3 e4]h; subst.
  { have eq:=h _ tym.
    apply: conv_pi... }
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 t e h; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_app_uniq Γ A B C m n s t :
  Γ ⊢ App m n : C ->
  (forall C Γ1 Γ2, Γ1 ∘ Γ2 => Γ -> Γ1 ⊢ m : C -> Pi A B s t === C) -> B.[n/] === C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s t e=>//{Γ x C}.
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn
     A0 B0 m0 n0 s0 t0[e1 e2]h; subst.
  { have/pi_inj[_[eq _]]:=h _ _ _ mrg tym.
    apply: conv_subst... }
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 t e h; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_fix_uniq Γ A B m : Γ ⊢ Fix A m : B -> A === B.
Proof with eauto.
  move e:(Fix A m)=>n ty. elim: ty A m e=>//{Γ B n}.
  move=>Γ A m k tyA ihA tym ihm A0 m0[e1 e2]; subst...
  move=>Γ A B m s eq tym ihm tyB ihB A0 m0 e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_unit_uniq Γ A : Γ ⊢ Unit : A -> Sort U === A.
Proof with eauto.
  move e:(Unit)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_it_uniq Γ A : Γ ⊢ It : A -> Unit === A.
Proof with eauto.
  move e:(It)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_either_uniq Γ A : Γ ⊢ Either : A -> Sort U === A.
Proof with eauto.
  move e:(Either)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_left_uniq Γ A : Γ ⊢ Left : A -> Either === A.
Proof with eauto.
  move e:(Left)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_right_uniq Γ A : Γ ⊢ Right : A -> Either === A.
Proof with eauto.
  move e:(Right)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_sigma_uniq Γ A B C s r t :
  Γ ⊢ Sigma A B s r t : C -> Sort t === C.
Proof with eauto.
  move e:(Sigma A B s r t)=>m ty. elim: ty A B s r t e=>//{Γ m C}.
  move=>Γ A B s r t leq k tyA ihA tyB ihB A0 B0 s0 r0 t0[e1 e2 e3 e4 e5]; subst...
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 r t e; subst.
  { apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma clc_pair_uniq Γ A B C m n s r t :
  Γ ⊢ Pair m n t : C ->
  [Γ] ⊢ A : Sort s ->
  [A :{s} Γ] ⊢ B : Sort r ->
  (forall Γ1 Γ2 G1 G2 X Y,
      Γ1 ⊢ m : X -> Γ1 ∘ G1 => Γ ->
      Γ2 ⊢ n : Y -> G2 ∘ Γ2 => Γ -> A === X /\ B.[m/] === Y) -> Sigma A B s r t === C.
Proof with eauto.
  move e:(Pair m n t)=>x ty. elim: ty m n A B s r t e=>//{Γ x C}.
  move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg1 tyS _ tym _ tyn _ m0 n0 A0 B0
    s0 r0 t0[e1 e2 e3]tyA0 tyB0 h; subst.

(* Lemma clc_app_uniq Γ A B C m n s t : *)
(*   Γ ⊢ App m n : C -> *)
(*   (forall C Γ1 Γ2, Γ1 ∘ Γ2 => Γ -> Γ1 ⊢ m : C -> Pi A B s t === C) -> B.[n/] === C. *)

(*   ihm : ∀ (Γ2 G1 G2 Γ : context term) (B : term), Γ2 ⊢ m : B → Γ1 ∘ G1 => Γ → Γ2 ∘ G2 => Γ → A === B *)
(*   tyn : Γ2 ⊢ n : B.[m/] *)
(*   ihn : ∀ (Γ3 G1 G2 Γ : context term) (B0 : term), Γ3 ⊢ n : B0 → Γ2 ∘ G1 => Γ → Γ3 ∘ G2 => Γ → B.[m/] === B0 *)
(*   Γ0, G1, G2, Γ3 : context term *)
(*   B0 : term *)
(*   tyP : Γ0 ⊢ Pair m n t : B0 *)

Lemma clc_uniq Γ1 Γ2 G1 G2 Γ m A B :
  Γ1 ⊢ m : A -> Γ2 ⊢ m : B ->
  Γ1 ∘ G1 => Γ -> Γ2 ∘ G2 => Γ -> A === B.
Proof with eauto.
  move=>ty. elim: ty Γ2 G1 G2 Γ B=>{Γ1 m A}.
  { move=>*. apply: clc_sort_uniq... }
  { move=>*. apply: clc_pi_uniq... }
  { move=>Γ x A s hs Γ2 G1 G2 Γ0 B tyV mrg1 mrg2.
    have[X[t[hsx eq]]]:=var_inv tyV.
    have[-> _//]:=clc_has_subset hs hsx mrg1 mrg2. }
  { move=>Γ A B m s t k tyP ihP tym ihm Γ2 G1 G2 Γ0 B0 tyL mrg1 mrg2.
    apply: clc_lam_uniq...
    move=>C tym'.
    destruct s.
    have{}mrg1: A :U Γ ∘ A :U G1 => A :U Γ0 by constructor.
    have{}mrg2: A :U Γ2 ∘ A :U G2 => A :U Γ0 by constructor.
    apply: ihm...
    have{}mrg1: A :L Γ ∘ _: G1 => A :L Γ0 by constructor.
    have{}mrg2: A :L Γ2 ∘ _: G2 => A :L Γ0 by constructor.
    apply: ihm... }
  { move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn Γ0 G1 G2 Γ3 B0 tyA mrg1 mrg2.
    have[D[mrg3 mrg4]]:=merge_splitR mrg1 mrg.
    apply: clc_app_uniq...
    move=>C Γ4 Γ5 mrg5 tym'.
    have[Dx[mrg6 mrg7]]:=merge_splitR mrg2 mrg5.
    apply: ihm.
    apply: tym'.
    apply: mrg4.
    apply: mrg7. }
  { move=>Γ A m k tyA ihA tym ihm Γ2 G1 G2 Γ0 B tyF mrg1 mrg2.
    apply: clc_fix_uniq... }
  { move=>Γ k Γ1 G1 G2 Γ0 B tyU mrg1 mrg2.
    apply: clc_unit_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyI mrg1 mrg2.
    apply: clc_it_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyE mrg1 mrg2.
    apply: clc_either_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyL mrg1 mrg2.
    apply: clc_left_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyR mrg1 mrg2.
    apply: clc_right_uniq... }
  { move=>Γ A B s r t leq k tyA ihA tyB ihB Γ2 G1 G2 Γ0 B0 tyS mrg1 mrg2.
    apply: clc_sigma_uniq... }
  { move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg tyS ihS tym ihm tyn ihn Γ0 G1 G2 Γ3 B0 tyP mrg1 mrg2.
    apply: clc_pair_uniq...
    admit.
    admit.
    intros.
    split.
    have[D1[mrg3 mrg4]]:=merge_splitR mrg1 mrg.
    have[D2[mrg5 mrg6]]:=merge_splitR mrg2 H0.
    apply: ihm.
    exact: H.
    exact: mrg4.
    exact: mrg6.
    have[D1[mrg3 mrg4]]:=merge_splitR mrg1 (merge_sym mrg).
    have[D2[mrg5 mrg6]]:=merge_splitR mrg2 (merge_sym H2).
    apply: ihn.
    exact: H1.
    exact: mrg4.
    exact: mrg6.


    
  }
