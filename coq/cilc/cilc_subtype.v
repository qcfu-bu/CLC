From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS cilc_context cilc_ast cilc_confluence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "s @ l" := (Sort s l) (at level 30).

Inductive sub1 : term -> term -> Prop :=
| sub1_refl A : 
  sub1 A A
| sub1_Sort s l1 l2 : 
  l1 <= l2 -> 
  sub1 (s @ l1) (s @ l2)
| sub1_Arrow A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (Arrow A B1 s) (Arrow A B2 s)
| sub1_Lolli A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (Lolli A B1 s) (Lolli A B2 s).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : 
  sub1 A' B' -> A === A' -> B' === B -> sub A B.
Notation "A <: B" := (sub A B) (at level 50, no associativity).

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_Sort s n m : n <= m -> s @ n <: s @ m.
Proof. move=> leq. exact/sub1_sub/sub1_Sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto 6 using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D=>{A B}
    [ A C D 
    | s l1 l2 leq C D conv sb
    | A B1 B2 s sb1 ih C D conv sb2
    | A B1 B2 s sb1 ih C D conv sb2 ]...
  inv sb; try (exfalso; solve_conv)...
    move: conv => /Sort_inj [->eq].
    apply: sub_Sort. subst.
    exact: leq_trans leq _.
  inv sb2; try (exfalso; solve_conv)...
    move: conv => /Arrow_inj[conv1 [conv2 ->]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    eapply SubI.
    eapply sub1_Arrow...
    eapply conv_Arrow...
    exact: conv_Arrow.
  inv sb2; try (exfalso; solve_conv)...
    move: conv => /Lolli_inj[conv1 [conv2 ->]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    eapply SubI. 
    eapply sub1_Lolli...
    eapply conv_Lolli...
    exact: conv_Lolli.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_Sort_inv s1 s2 l1 l2 :
  s1 @ l1 <: s2 @ l2 -> s1 = s2 /\ l1 <= l2.
Proof.
  move=> [s1' s2' []].
  move=> A c1 c2.
    have{c1 c2}/Sort_inj[s l]: s1 @ l1 === s2 @ l2.
      exact: conv_trans c2.
    inv l=> //.
  move=> s l0 l3 leq /Sort_inj[->->] /Sort_inj[<-<-] => //.
  move=> *. exfalso; solve_conv.
  move=> *. exfalso; solve_conv.
Qed.

Lemma sub_Sort_False1 l1 l2 : ~Sort U l1 <: Sort L l2.
Proof.
  move=> [s1 s2 []].
  move=> A e1 e2.
    have e : Sort U l1 === Sort L l2.
      exact: conv_trans e2.
    solve_conv.
  move=> s l3 l4 _ /Sort_inj[<- _] h. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
Qed.

Lemma sub_Sort_False2 l1 l2 : ~Sort L l1 <: Sort U l2.
Proof.
  move=> [s1 s2 []].
  move=> A e1 e2.
    have e : Sort L l1 === Sort U l2.
      exact: conv_trans e2.
    solve_conv.
  move=> s l3 l4 _ /Sort_inj[<- _] h. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
Qed.

Lemma sub_Arrow_inv A1 A2 s1 s2 B1 B2 :
  Arrow A1 B1 s1 <: Arrow A2 B2 s2 -> 
  A1 === A2 /\ B1 <: B2 /\ s1 = s2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/Arrow_inj[c1 [c2 ->]]: 
      Arrow A1 B1 s1 === Arrow A2 B2 s2.
     exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> A B0 B3 s sb /Arrow_inj[c1 [c2 <-]]. 
    move=> /Arrow_inj[c3 [c4 ->]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_Lolli_inv A1 A2 s1 s2 B1 B2 :
  Lolli A1 B1 s1 <: Lolli A2 B2 s2 -> 
  A1 === A2 /\ B1 <: B2 /\ s1 = s2.
Proof.
  move=> [A' B' []].
  move=> C c1 c2. 
    have{c1 c2}/Lolli_inj[c1 [c2 ->]]: 
      Lolli A1 B1 s1 === Lolli A2 B2 s2.
      exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  move=> *. exfalso; solve_conv.
  move=> *. exfalso; solve_conv.
  move=> A B0 B3 s sb /Lolli_inj[c1 [c2 <-]]. 
    move=> /Lolli_inj[c3 [c4 ->]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst σ A B : sub1 A B -> sub1 A.[σ] B.[σ].
Proof. move=> s. elim: s σ => /=; eauto using sub1. Qed.

Lemma sub_subst σ A B : A <: B -> A.[σ] <: B.[σ].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Lemma sub_ren A B ξ : A <: B -> A.[ren ξ] <: B.[ren ξ].
Proof. move=> *; by apply: sub_subst. Qed.