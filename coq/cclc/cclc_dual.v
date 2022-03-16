From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_typing clc_confluence
  cclc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dual0 : term -> term -> Prop :=
| dual0_end : dual0 InpEnd OutEnd
| dual0_endi : dual0 OutEnd InpEnd
| dual0_com A B1 B2 s :
  dual0 B1 B2 ->
  dual0 (Inp A B1 s) (Out A B2 s)
| dual0_comi A B1 B2 s :
  dual0 B1 B2 ->
  dual0 (Out A B1 s) (Inp A B2 s).

Inductive dual : term -> term -> Prop :=
| dual_dual0 A B : 
  dual0 A B -> dual A B 
| dual_conv A A' B' B : 
  A === A' -> dual A' B' -> B' === B -> dual A B.

Notation "m ~ n" := (dual m n) (at level 30).

Lemma dual0_sym A B : dual0 A B -> dual0 B A.
Proof.
  elim; eauto using dual0.
Qed.

Lemma dual0_inj A B C : 
  dual0 A B -> dual0 A C -> B = C.
Proof with eauto.
  move=> h.
  elim: h C=>{A B}.
  move=>C d. inv d...
  move=>C d. inv d...
  move=>A B1 B2 s d1 ih C d2. 
    inv d2. erewrite ih...
  move=>A B1 B2 s d1 ih C d2. 
    inv d2. erewrite ih...
Qed.

Lemma dual_sym A B : A ~ B -> B ~ A.
Proof.
  elim; eauto using dual, dual0_sym, conv_sym.
Qed.

Lemma dual_end A B :
  A ~ B -> InpEnd === A -> OutEnd === B.
Proof with eauto.
  elim=>{A B}.
  move=>A B d c.
  destruct A; try inv d...
  all: try solve[exfalso; solve_conv].
  move=>A A' B' B c1 d ih c2 c3.
  apply: conv_trans.
  apply: ih.
  apply: conv_trans.
  exact: c3.
  exact: c1.
  exact: c2.
Qed.

Lemma dual_endi A B :
  A ~ B -> OutEnd === A -> InpEnd === B.
Proof with eauto.
  elim=>{A B}.
  move=>A B d c.
  destruct A; try inv d...
  all: try solve[exfalso; solve_conv].
  move=>A A' B' B c1 d ih c2 c3.
  apply: conv_trans.
  apply: ih.
  apply: conv_trans.
  exact: c3.
  exact: c1.
  exact: c2.
Qed.

Lemma dual_com X Y A B1 s :
  X ~ Y -> 
  Inp A B1 s === X -> 
  exists2 B2, Out A B2 s === Y & B1 ~ B2.
Proof.
  move=>h.
  elim: h A B1 s=>{X Y}.
  move=>A B d ih B1 s c.
    destruct A; try inv d.
    all: try solve[exfalso; solve_conv].
    have[c1[c2 e]]:=inp_inj c; subst.
    exists B3; eauto using dual with conv_congr.
  move=>A A' B' B c1 d1 ih c2 A0 B1 s c3.
    have c4:=conv_trans _ c3 c1.
    have[B2 c5 d2]:=ih _ _ _ c4.
    exists B2; eauto using conv_trans.
Qed.

Lemma dual_comi X Y A B1 s :
  X ~ Y -> 
  Out A B1 s === X -> 
  exists2 B2, Inp A B2 s === Y & B1 ~ B2.
Proof.
  move=>h.
  elim: h A B1 s=>{X Y}.
  move=>A B d ih B1 s c.
    destruct A; try inv d.
    all: try solve[exfalso; solve_conv].
    have[c1[c2 e]]:=out_inj c; subst.
    exists B3; eauto using dual with conv_congr.
  move=>A A' B' B c1 d1 ih c2 A0 B1 s c3.
    have c4:=conv_trans _ c3 c1.
    have[B2 c5 d2]:=ih _ _ _ c4.
    exists B2; eauto using conv_trans.
Qed.

Lemma dual_inj' A B C :
  dual0 A B -> A ~ C -> B === C.
Proof.
  move=> h.
  elim: h C=>{A B}.
  move=>C d. apply: dual_end; eauto.
  move=>C d. apply: dual_endi; eauto.
  move=>A B1 B2 s d1 ih C d2.
    have[B3 c1/ih c2{ih}]:=dual_com d2 (convR _ _).
    apply: conv_trans.
    apply: conv_out; eauto.
    exact: c1.
  move=>A B1 B2 s d1 ih C d2.
    have[B3 c1/ih c2{ih}]:=dual_comi d2 (convR _ _).
    apply: conv_trans.
    apply: conv_inp; eauto.
    exact: c1.
Qed.

Lemma dual_inj A B C :
  A ~ B -> A ~ C -> B === C.
Proof.
  move=>h.
  elim: h C=>{A B}.
  move=>A B d1 C d2. apply: dual_inj'; eauto.
  move=>A A' B' B c1 d1 ih c2 C d2.
    apply: conv_trans.
    apply: conv_sym.
    exact: c2.
    apply: ih.
    apply: dual_conv.
    apply: conv_sym; eauto.
    exact: d2.
    eauto.
Qed.
