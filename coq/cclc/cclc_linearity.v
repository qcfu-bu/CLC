From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_linearity
  cclc_ast cclc_dual cclc_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint occurs (i : nat) (p : proc) : nat :=
  match p with
  | ⟨ m ⟩ => clc_linearity.occurs i m
  | p ∣ q => occurs i p + occurs i q
  | ν.p => occurs i.+2 p
  end.

Theorem narity Γ p i : 
  Γ ⊢ p -> of_sort Γ i None -> occurs i p = 0.
Proof.
  move=>ty. elim: ty i=>//={Γ p}.
  move=>Γ m A s tym i os.
    apply: narity; eauto.
  move=>Γ1 Γ2 Γ p q mrg typ ihp tyq ihq i os.
    have[os1 os2]:=of_sortN_merge_inv mrg os.
    rewrite ihp; eauto.
  move=>Γ p A B d tyA tyB i typ ihp x os. 
    apply: ihp.
    repeat econstructor; eauto.
Qed.

Theorem linearity Γ p i : 
  Γ ⊢ p -> of_sort Γ i (Some L) -> occurs i p = 1.
Proof.
  move=>ty. elim: ty i=>//={Γ p}.
  move=>Γ m A s tym i os.
    apply: linearity; eauto.
  move=>Γ1 Γ2 Γ p q mrg typ ihp tyq ihq i os.
    have[[os1 os2]|[os1 os2]]:=of_sortL_merge_inv mrg os.
    rewrite ihp; eauto.
    erewrite narity; eauto.
    erewrite narity; eauto.
  move=>Γ p A B d tyA tyB i typ ihp x os.
    apply: ihp.
    repeat econstructor; eauto.
Qed.

Lemma iren_occurs i p ξ :
  iren i ξ -> occurs i p.[ren ξ] = 0.
Proof.
  elim: p i ξ=>//=.
  move=>m i ξ ir.
    apply: clc_linearity.iren_occurs; eauto.
  move=>p ihp q ihq i ξ ir.
    rewrite ihp; eauto.
  move=>p ihp i ξ ir; asimpl.
    rewrite ihp; eauto.
    have->:
      (0 .: 1 .: ξ >>> (+2)) = (upren (upren ξ))
      by autosubst.
    apply: iren_upren.
    by apply: iren_upren.
Qed.