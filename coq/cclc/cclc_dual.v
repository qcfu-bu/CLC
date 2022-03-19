From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_typing clc_confluence
  cclc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dual : term -> term -> Prop :=
| dual_end : dual InpEnd OutEnd
| dual_endi : dual OutEnd InpEnd
| dual_com A B1 B2 s :
  dual B1 B2 ->
  dual (Inp A B1 s) (Out A B2 s)
| dual_comi A B1 B2 s :
  dual B1 B2 ->
  dual (Out A B1 s) (Inp A B2 s).

Notation "m ~ n" := (dual m n) (at level 30).

Lemma dual_sym A B : A ~ B -> B ~ A.
Proof.
  elim; eauto using dual.
Qed.

Lemma dual_inj A B C :
  A ~ B -> A ~ C -> B === C.
Proof.
  move=>h.
  elim: h C=>{A B}.
  move=>C d. inv d; eauto.
  move=>C d. inv d; eauto.
  move=>A B1 B2 s d1 ih C d2. inv d2.
  have e:=ih _ H3. apply: conv_out; eauto.
  move=>A B1 B2 s d1 ih C d2. inv d2.
  have e:=ih _ H3. apply: conv_inp; eauto.
Qed.
