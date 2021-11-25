From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion cilc_arity_spine
  cilc_validity cilc_typing_spine cilc_respine cilc_iota_lemma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Nat := 
  Ind (U @ 0) [:: Var 0; Prod (Var 0) (Var 1) U ] U.

Lemma Nat_type : [ nil |- Nat :- U @ 0 ].
Proof.
  econstructor.
  { constructor. }
  { constructor.
    { replace (Var 0) with (spine (Var 0) nil) by eauto.
      repeat constructor. }
    { constructor.
      constructor.
      replace (Var 0) with (spine (Var 0) nil) by eauto.
      repeat constructor.
      replace (Var 1) with (spine (Var 1) nil) by eauto.
      repeat constructor.
      constructor.
      discriminate.
      constructor. } }
  { constructor. }
  { repeat constructor. }
  { have sb : U @ 0 <: U @ 1.
      apply: sub_Sort; eauto.
    constructor.
    apply: s_Conv; eauto.
    repeat constructor.
    repeat constructor.
    repeat constructor.
    have ty : [Var 0 +u ((U @ 0) +u [::]) |- Var 1 :- U @ 1].
      apply: s_Conv; eauto.
      repeat constructor.
      constructor.
      replace (U @ 0) with (U @ 0).[ren (+1)] by eauto.
      constructor; simpl.
      replace (U @ 0) with (U @ 0).[ren (+1)] by eauto.
      repeat constructor.
    apply: u_Prod.
    repeat constructor.
    apply: s_Conv; eauto.
    repeat constructor.
    repeat constructor.
    apply: ty. }
Qed.
Hint Resolve Nat_type.

Definition Zero := Constr 0 Nat.

Lemma Zero_type : [ nil |- Zero :- Nat ].
Proof.
  replace Nat with (spine (Var 0) nil).[Nat/] by eauto.
  repeat constructor; eauto.
Qed.
Hint Resolve Zero_type.

Definition Succ := Constr 1 Nat.

Lemma Succ_type : [ nil |- Succ :- Prod Nat Nat U ].
Proof.
  replace (Prod Nat Nat U) with (Prod (Var 0) (Var 1) U).[Nat/] by eauto.
  repeat constructor; eauto.
Qed.
Hint Resolve Succ_type.

Definition LUnit := Ind (L @ 0) [:: Var 0] L.

Lemma LUnit_type : [ nil |- LUnit :- L @ 0 ].
Proof.
  econstructor.
  { constructor. }
  { repeat constructor. 
    replace (Var 0) with (spine (Var 0) nil) by eauto.
    repeat constructor. }
  { constructor. }
  { repeat constructor. }
  { constructor.

  }
  