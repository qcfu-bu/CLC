From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive of_sort : context term -> nat -> option sort -> Prop :=
| of_sortTy Γ A s :
  of_sort (A :{s} Γ) 0 (Some s)
| of_sortN Γ :
  of_sort (_: Γ) 0 None
| of_sortS Γ A i s :
  of_sort Γ i s ->
  of_sort (A :: Γ) i.+1 s.

Fixpoint occurs (i : nat) (m : term) : nat :=
  match m with
  | Var x => if x == i then 1 else 0
  | Sort _ _ => 0
  | Pi A B _ _ _ => occurs i A + occurs i.+1 B
  | Lam A m _ _ => occurs i A + occurs i.+1 m
  | App m n => occurs i m + occurs i n
  | Unit => 0
  | It => 0
  | Sigma A B _ _ _ => occurs i A + occurs i.+1 B
  | Pair m n _ => occurs i m + occurs i n
  | LetIn1 m n => occurs i m + occurs i n
  | LetIn2 m n => occurs i m + occurs i.+2 n
  | Ptr _ => 0
  end.

Lemma of_sortL_impure Γ i : of_sort Γ i (Some L) -> ~Γ |> U.
Proof with eauto using key.
  move e:(Some L)=>s os.
  elim: os e=>//={Γ i s}. 
  move=>Γ A s[<-]k. inv k.
  move=>Γ A i s os ih e k. inv k.
  apply: ih...
  apply: ih...
Qed.

Lemma of_sortL_hasU Γ i x A : of_sort Γ i (Some L) -> ~has Γ x U A.
Proof.
  move e:(Some L)=>s os. elim: os e x A=>//={Γ i s}.
  move=>Γ A s e x B hs. inv hs. inv e. inv e.
  move=>Γ A i s os ih e x B hs. inv hs.
    apply: of_sortL_impure; eauto.
    apply:ih; eauto.
    apply:ih; eauto.
Qed.

Lemma of_sortL_hasL Γ i x A : 
  of_sort Γ i (Some L) -> has Γ x L A -> x = i.
Proof.
  move e:(Some L)=>s os. elim: os e x A=>//={Γ i s}.
  move=>Γ A s e x B hs. inv hs=>//.
  move=>Γ A i s os ih e x B hs. inv hs.
    exfalso. apply: of_sortL_impure; eauto.
    erewrite<-ih; eauto.
    erewrite<-ih; eauto.
Qed.

Lemma of_sortN_re Γ i : of_sort Γ i None -> of_sort [Γ] i None.
Proof with eauto using of_sort.
  move e:(None)=>s os. elim: os e=>//={Γ i s}...
  move=>Γ A i s os1 ih /ih os2.
  destruct A...
  destruct p.
  destruct s0...
Qed.

Lemma of_sortL_reN Γ i : of_sort Γ i (Some L) -> of_sort [Γ] i None.
Proof.
  move e:(Some L)=>s os. elim: os e=>//{Γ i s}.
  move=>Γ A s [<-]//=. by constructor.
  move=>Γ [[A[|]]|] i [t|] os ih//=[e]; subst.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

Lemma of_sortN_has Γ i x s A :
  of_sort Γ i None -> has Γ x s A -> x == i = false.
Proof.
  move e:(None)=>t os. elim: os e x s A=>//={Γ i t}.
  move=>Γ _ x s A hs. inv hs=>//.
  move=>Γ A i s os ih e x t B hs. inv hs=>//.
    erewrite<-(ih erefl x0); eauto.
    erewrite<-(ih erefl x0); eauto.
Qed.

Lemma of_sortL_merge_inv Γ1 Γ2 Γ i :
  Γ1 ∘ Γ2 => Γ -> of_sort Γ i (Some L) ->
  (of_sort Γ1 i (Some L) /\ of_sort Γ2 i None) \/
  (of_sort Γ2 i (Some L) /\ of_sort Γ1 i None).
Proof with eauto 6 using of_sort.
  move=>mrg. elim: mrg i=>{Γ1 Γ2 Γ}.
  move=>i os. inv os.
  move=>Γ1 Γ2 Γ m mrg ih i os. inv os.
    move:(ih _ H3)=>{H3 ih}[[os1 os2]|[os1 os2]].
    left... right...
  move=>Γ1 Γ2 Γ m mrg ih i os. inv os.
    left...
    move:(ih _ H3)=>{H3 ih}[[os1 os2]|[os1 os2]].
    left... right...
  move=>Γ1 Γ2 Γ m mrg ih i os. inv os.
    right...
    move:(ih _ H3)=>{H3 ih}[[os1 os2]|[os1 os2]].
    left... right...
  move=>Γ1 Γ2 Γ mrg ih i os. inv os.
    move:(ih _ H3)=>{H3 ih}[[os1 os2]|[os1 os2]].
    left... right...
Qed.

Lemma of_sortN_merge_inv Γ1 Γ2 Γ i :
  Γ1 ∘ Γ2 => Γ -> of_sort Γ i None ->
    of_sort Γ1 i None /\ of_sort Γ2 i None.
Proof with eauto using of_sort.
  move=>mrg. elim: mrg i=>{Γ1 Γ2 Γ}.
  move=>i os. inv os.
  move=>Γ1 Γ2 Γ m mrg ih i os. inv os.
    move:(ih _ H3)=>{ih H3}[os1 os2]...
  move=>Γ1 Γ2 Γ m mrg ih i os. inv os.
    move:(ih _ H3)=>{ih H3}[os1 os2]...
  move=>Γ1 Γ2 Γ m mrg ih i os. inv os.
    move:(ih _ H3)=>{ih H3}[os1 os2]...
  move=>Γ1 Γ2 Γ mrg ih i os. inv os...
    move:(ih _ H3)=>{ih H3}[os1 os2]...
Qed.

Lemma narity Γ m A s i : 
  Γ ⊢ m : A : s -> of_sort Γ i None -> occurs i m = 0.
Proof with eauto using of_sort, of_sortN_re.
  move=>ty. elim: ty i=>//{Γ m A s}.
  move=>Γ A B s r t l k tyA ihA tyB ihB i os//=.
    rewrite ihA...
  move=>Γ x A s hs i os//=.
    erewrite of_sortN_has...
  move=>Γ A B m s r t l k tyP ihP tym ihm i os//=.
    move:(ihP _ (of_sortN_re os))=>//=e1.
    move:(ihm _ (of_sortS (Some (A, s)) os))=>e2.
    destruct (occurs i.+1 B).
    rewrite addn0 in e1.
    rewrite e1 e2...
    destruct (occurs i A); discriminate.
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn i os//=.
    move:(of_sortN_merge_inv mrg os)=>[os1 os2].
    rewrite ihm...
  move=>Γ A B s r t i leq k tyA ihA tyB ihB x os//=.
    rewrite ihA...
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg
    tyS ihS tym ihm tyn ihn x os//=.
    move:(of_sortN_merge_inv mrg os)=>[os1 os2].
    rewrite ihm...
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn ihn x os//=.
    move:(of_sortN_merge_inv mrg os)=>[os1 os2].
    rewrite ihm...
  move=>Γ1 Γ2 Γ A B C m n s r t k x l leq key mrg
    tym ihm tyC ihC tyn ihn i os//=.
    move:(of_sortN_merge_inv mrg os)=>[os1 os2].
    rewrite ihm...
Qed.

Theorem linearity Γ m A s i :
  Γ ⊢ m : A : s -> of_sort Γ i (Some L) -> occurs i m = 1.
Proof with eauto using of_sort.
  move=>ty. elim: ty i=>//{Γ m A s}.
  move=>Γ s l k i os.
    exfalso. apply: of_sortL_impure; eauto.
  move=>Γ A B s r t l k tyA ihA tyB ihB i os//=.
    exfalso. apply: of_sortL_impure; eauto.
  move=>Γ x A [|] hs i os//=.
    exfalso. apply: of_sortL_hasU; eauto.
    have->:=of_sortL_hasL os hs.
    by rewrite eq_refl.
  move=>Γ A B m s r [|] l k tyP ihP tym ihm i os//=.
    exfalso. apply: of_sortL_impure; eauto.
    have osN:=of_sortL_reN os.
    have//=e:=narity tyP osN.
    destruct (occurs i.+1 B).
    rewrite addn0 in e.
    rewrite e.
    erewrite ihm...
    destruct (occurs i A); discriminate.
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn i os//=.
    have[[os1 os2]|[os1 os2]]:=of_sortL_merge_inv mrg os.
    have->:=narity tyn os2.
    by rewrite ihm.
    have->:=narity tym os2.
    by rewrite ihn.
  move=>Γ k i os. exfalso. apply: of_sortL_impure; eauto.
  move=>Γ k i os. exfalso. apply: of_sortL_impure; eauto.
  move=>Γ A B s r t i leq k tyA ihA tyB ihB x os//=.
    exfalso. apply: of_sortL_impure; eauto.
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg 
    tyS ihS tym ihm tyn ihn x os//=.
    have[[os1 os2]|[os1 os2]]:=of_sortL_merge_inv mrg os.
    rewrite ihm... erewrite narity...
    rewrite ihn... erewrite narity...
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn ihn i os//=.
    have[[os1 os2]|[os1 os2]]:=of_sortL_merge_inv mrg os.
    rewrite ihm... erewrite narity...
    rewrite ihn... erewrite narity...
  move=>Γ1 Γ2 Γ A B C m n s r t k x l leq keq mrg
    tym ihm tyC ihC tyn ihn i os//=.
    have[[os1 os2]|[os1 os2]]:=of_sortL_merge_inv mrg os.
    rewrite ihm... erewrite narity...
    rewrite ihn... erewrite narity...
Qed.
    