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
  | Proto _ => 0
  | InpEnd => 0
  | OutEnd => 0
  | Inp A B s => occurs i A + occurs i.+1 B
  | Out A B s => occurs i A + occurs i.+1 B
  | Ch A => occurs i A
  | Recv ch => occurs i ch
  | Send ch => occurs i ch
  | Close ch => occurs i ch
  | Wait ch => occurs i ch
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
  move=>Γ A B s i k tyA ihA tyB ihB i0 os//=.
    rewrite ihA...
  move=>Γ A B s i k tyA ihA tyB ihB i0 os//=.
    rewrite ihA...
Qed.

Theorem linearity Γ m A s i :
  Γ ⊢ m : A : s -> of_sort Γ i (Some L) -> occurs i m = 1.
Proof with eauto using of_sort.
  move=>ty. elim: ty i=>//{Γ m A s}.
  move=>Γ s l k i os.
    exfalso. apply: of_sortL_impure...
  move=>Γ A B s r t l k tyA ihA tyB ihB i os//=.
    exfalso. apply: of_sortL_impure...
  move=>Γ x A [|] hs i os//=.
    exfalso. apply: of_sortL_hasU...
    have->:=of_sortL_hasL os hs.
    by rewrite eq_refl.
  move=>Γ A B m s r [|] l k tyP ihP tym ihm i os//=.
    exfalso. apply: of_sortL_impure...
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
  move=>Γ k i os. exfalso. apply: of_sortL_impure...
  move=>Γ k i os. exfalso. apply: of_sortL_impure...
  move=>Γ A B s r t i leq k tyA ihA tyB ihB x os//=.
    exfalso. apply: of_sortL_impure...
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
  move=>Γ i k l os. exfalso. apply: of_sortL_impure...
  move=>Γ i k l os. exfalso. apply: of_sortL_impure...
  move=>Γ i k l os. exfalso. apply: of_sortL_impure...
  move=>Γ A B s i k tyA ihA tyB ihB l os.
    exfalso. apply: of_sortL_impure...
  move=>Γ A B s i k tyA ihA tyB ihB l os.
    exfalso. apply: of_sortL_impure...
Qed.
    
Definition iren i (ξ : var -> var) := forall x, ~ξ x == i.

Lemma iren0 : iren 0 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren1 : iren 1 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren_upren i ξ : iren i ξ -> iren i.+1 (upren ξ).
Proof.
  move=> ir x.
  elim: x.
  asimpl; eauto.
  asimpl=>n e; eauto.
Qed.

Lemma iren_occurs i m ξ :
  iren i ξ -> occurs i m.[ren ξ] = 0.
Proof with eauto using iren_upren.
  elim: m i ξ...
  move=>x i ξ ir.
    unfold occurs; simpl.
    have{}ir:=ir x.
    move e:(ξ x == i)=>[|]//.
  move=>A ihA B ihB s r t i ξ ir; asimpl.
    rewrite ihA...
  move=>A ihA m ihm s t i ξ ir; asimpl.
    rewrite ihA...
  move=>m ihm n ihn i ξ ir; asimpl.
    rewrite ihm...
  move=>A ihA B ihB s r t i ξ ir; asimpl.
    rewrite ihA...
  move=>m ihm n ihn t i ξ ir; asimpl.
    rewrite ihm...
  move=>m ihm n ihn i ξ ir; asimpl.
    rewrite ihm...
  move=>m ihm n ihn i ξ ir; asimpl.
    rewrite ihm...
    rewrite ihn...
    have->:(0 .: 1 .: ξ >>> (+2)) = (upren (upren ξ)) 
      by autosubst...
  move=>A ihA B ihB s i ξ ir; asimpl.
    rewrite ihA...
  move=>A ihA B ihB s i ξ ir; asimpl.
    rewrite ihA...
Qed.

Inductive nsubst : nat -> (var -> term) -> Prop :=
| Nsubst i σ :
  (forall x, x < i -> σ x = Var x) ->
  (forall x, i < x -> (σ x).[ren (+1)] = Var x) ->
  nsubst i σ.

Lemma nsubst0 m : nsubst 0 (m .: ids).
Proof.
  constructor.
  elim=>//.
  elim=>//.
Qed.

Lemma nsubst_up i σ : nsubst i σ -> nsubst i.+1 (up σ).
Proof.
  constructor.
  move=>x. elim: x i σ H=>//.
  move=>n _ i σ ns lt; asimpl. inv ns.
  rewrite H; eauto.
  move=>x. elim: x i σ H=>//.
  move=>n _ i σ ns lt; asimpl. inv ns.
  replace (σ n).[ren (+2)] 
    with (σ n).[ren (+1)].[ren (+1)] by autosubst.
  rewrite H0; eauto.
Qed.

Lemma nsubst_occurs m i σ1 σ2 :
  occurs i m = 0 -> nsubst i σ1 -> nsubst i σ2 -> m.[σ1] = m.[σ2].
Proof with eauto using nsubst_up.
  elim: m i σ1 σ2=>//=.
  move=>x i σ1 σ2 e ns1 ns2. 
  inv ns1. inv ns2.
  { move: e.
    move e1:(x == i)=>[|]_//.
    have {}e1:x != i by rewrite e1.
    rewrite neq_ltn in e1.
    have{e1}[lt|lt]:=orP e1.
    have->:=H _ lt.
    by have->:=H1 _ lt.
    have e1:=H0 _ lt.
    have e2:=H2 _ lt.
    have: 
      (σ1 x).[ren (+1)].[ren (subn^~ 1)] = (Var x).[ren (subn^~ 1)].
      by rewrite e1.
    asimpl.
    have->:((+1) >>> subn_rec^~ 1) = id.
      f_ext. elim; asimpl=>//.
    asimpl=>->.
    have: 
      (σ2 x).[ren (+1)].[ren (subn^~ 1)] = (Var x).[ren (subn^~ 1)].
      by rewrite e2.
    asimpl.
    have->:((+1) >>> subn_rec^~ 1) = id.
      f_ext. elim; asimpl=>//.
    asimpl=>->//. }
  move=>A ihA B ihB s r t i σ1 σ2 oc ns1 ns2.
  { remember (occurs i A); remember (occurs i.+1 B).
    destruct n; destruct n0; try discriminate.
    f_equal... }
  move=>A ihA m ihm s t i σ1 σ2 oc ns1 ns2.
  { remember (occurs i A); remember (occurs i.+1 m).
    destruct n; destruct n0; try discriminate.
    f_equal... }
  move=>m ihm n ihn i σ1 σ2 oc ns1 ns2.
  { remember (occurs i m); remember (occurs i n).
    destruct n0; destruct n1; try discriminate.
    f_equal... }
  move=>A ihA B ihB s r t i σ1 σ2 oc ns1 ns2.
  { remember (occurs i A); remember (occurs i.+1 B).
    destruct n; destruct n0; try discriminate.
    f_equal... }
  move=>m ihm n ihn t i σ1 σ2 oc ns1 ns2.
  { remember (occurs i m); remember (occurs i n).
    destruct n0; destruct n1; try discriminate.
    f_equal... }
  move=>m ihm n ihn i σ1 σ2 oc ns1 ns2.
  { remember (occurs i m); remember (occurs i n).
    destruct n0; destruct n1; try discriminate.
    f_equal... }
  move=>m ihm n ihn i σ1 σ2 oc ns1 ns2.
  { remember (occurs i m); remember (occurs i.+2 n).
    destruct n0; destruct n1; try discriminate.
    f_equal... 
    replace (upn 2 σ1) with (up (up σ1)) by autosubst.
    replace (upn 2 σ2) with (up (up σ2)) by autosubst.
    apply: ihn... }
  move=>A ihA B ihB s i σ1 σ2 oc ns1 ns2.
  { remember (occurs i A); remember (occurs i.+1 B).
    destruct n; destruct n0; try discriminate.
    f_equal... }
  move=>A ihA B ihB s i σ1 σ2 oc ns1 ns2.
  { remember (occurs i A); remember (occurs i.+1 B).
    destruct n; destruct n0; try discriminate.
    f_equal... }
  move=>A ihA i σ1 σ2 oc ns1 ns2. f_equal...
  move=>ch ihc i σ1 σ2 oc ns1 ns2. f_equal...
  move=>ch ihc i σ1 σ2 oc ns1 ns2. f_equal...
  move=>ch ihc i σ1 σ2 oc ns1 ns2. f_equal...
  move=>ch ihc i σ1 σ2 oc ns1 ns2. f_equal...
Qed.

Lemma nsubst_subst m n1 n2 :
  occurs 0 m = 0 -> m.[n1/] = m.[n2/].
Proof.
  move=>oc.
  apply: nsubst_occurs; eauto.
  apply: nsubst0.
  apply: nsubst0.
Qed.