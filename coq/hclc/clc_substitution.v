From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Δ ⊢ σ ⊣ Γ" (at level 50, σ, Γ at next level).

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil σ :
  nil ⊢ σ ⊣ nil
| agree_subst_ty Δ σ Γ s A :
  Δ ⊢ σ ⊣ Γ ->
  A.[σ] :{s} Δ ⊢ up σ ⊣ A :{s} Γ
| agree_subst_n Δ σ Γ :
  Δ ⊢ σ ⊣ Γ ->
  _: Δ ⊢ up σ ⊣ _: Γ
| agree_subst_wkU Δ σ Γ n A :
  Δ ⊢ σ ⊣ Γ ->
  [Δ] ⊢ n : A.[σ] : U ->
  Δ ⊢ n .: σ ⊣ A :U Γ
| agree_subst_wkL Δ1 Δ2 Δ σ Γ n A :
  Δ1 ∘ Δ2 => Δ ->
  Δ1 ⊢ σ ⊣ Γ ->
  Δ2 ⊢ n : A.[σ] : L ->
  Δ ⊢ n .: σ ⊣ A :L Γ
| agree_subst_wkN Δ σ Γ n :
  Δ ⊢ σ ⊣ Γ ->
  Δ ⊢ n .: σ ⊣ _: Γ
| agree_subst_conv Δ σ Γ A B s l :
  A <: B ->
  [Δ] ⊢ B.[ren (+1)].[σ] : s @ l : U ->
  [Γ] ⊢ B : s @ l : U ->
  Δ ⊢ σ ⊣ A :{s} Γ ->
  Δ ⊢ σ ⊣ B :{s} Γ
where "Δ ⊢ σ ⊣ Γ" := (agree_subst Δ σ Γ).

Lemma agree_subst_key Δ σ Γ s :
  Δ ⊢ σ ⊣ Γ -> Γ |> s -> Δ |> s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Δ σ Γ}...
  move=>Δ σ Γ s A agr ih t k. inv k...
  move=>Δ σ Γ agr ih t k. inv k...
  move=>Δ σ Γ n A agr ih tyn t k. inv k...
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr ih tyn t k. inv k.
    move:(ih _ H3)=>{H3}ih.
    apply: merge_impureL...
  move=>Δ1 Δ2 Δ σ agr ih t k. inv k...
  move=>Δ σ Γ A B s l sb tyB1 tyB2 agr ih t k. inv k...
Qed.

Lemma agree_subst_refl Γ : Γ ⊢ ids ⊣ Γ.
Proof with eauto using agree_subst.
  elim: Γ...
  move=>[[A s]|] Γ agr.
  have: A.[ids] :{s} Γ ⊢ up ids ⊣ A :{s} Γ... by asimpl.
  have: _: Γ ⊢ up ids ⊣ _: Γ... by asimpl.
Qed.
Hint Resolve agree_subst_refl.

Lemma agree_subst_has Δ σ Γ x s A :
  Δ ⊢ σ ⊣ Γ -> has Γ x s A -> Δ ⊢ σ x : A.[σ] : s.
Proof with eauto using agree_subst, agree_subst_key.
  move=> agr. elim: agr x s A=>{Δ σ Γ}.
  move=>σ x s A hs. inv hs.
  move=>Δ σ Γ s A agr ih x t B hs. inv hs.
  { asimpl.
    replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] 
      by autosubst.
    apply: clc_var.
    constructor... }
  { asimpl.
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] 
      by autosubst.
    apply: eweakeningU... }
  move=>Δ σ Γ agr ih x s A hs. inv hs.
  { asimpl. 
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] 
      by autosubst.
    apply: eweakeningN... }
  move=>Δ σ Γ n A agr ih tyn x s B hs. inv hs.
  { asimpl.
    rewrite<-pure_re in tyn... }
  { asimpl... }
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr ih tyn x s B hs. inv hs.
  { asimpl.
    move:(agree_subst_key agr H5)=>{H5}k.
    have->:=(merge_pureL mrg k)... }
  move=>Δ σ Γ n agr ih x s A hs. inv hs.
  { asimpl... }
  move=>Δ σ Γ A B s l sb tyB1 tyB2 agr ih x t C hs. inv hs.
  { apply: clc_conv. 
    apply: sub_subst.
    apply: sub_ren...
    apply: ih.
    constructor...
    eauto. }
  { apply: ih.
    constructor... }
Qed.

Lemma agree_subst_re Δ σ Γ : Δ ⊢ σ ⊣ Γ -> [Δ] ⊢ σ ⊣ [Γ].
Proof with eauto using agree_subst, agree_subst_key.
  elim=>{Δ σ Γ}...
  move=>Δ σ Γ [] A agr1 agr2//=...
  move=>Δ σ Γ n A agr1 agr2 ty//=.
    apply: agree_subst_wkU...
    by rewrite<-re_invo.
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr1 agr2 tyn//=.
    apply: agree_subst_wkN...
    move: (merge_re_re mrg)=>[_[<-_]]...
  move=>Δ σ Γ A B [] l sb tyB1 tyB2 agr1 agr2//=.
    apply: agree_subst_conv...
    rewrite<-re_invo...
    rewrite<-re_invo...
Qed.

Lemma merge_agree_subst_inv Δ σ Γ1 Γ2 Γ :
  Δ ⊢ σ ⊣ Γ -> Γ1 ∘ Γ2 => Γ ->
  exists Δ1 Δ2,
    Δ1 ∘ Δ2 => Δ /\ Δ1 ⊢ σ ⊣ Γ1 /\ Δ2 ⊢ σ ⊣ Γ2.
Proof with eauto 6 using merge, agree_subst, agree_subst_key.
  move=>agr. elim: agr Γ1 Γ2=>{Δ σ Γ}.
  move=>σ Γ1 Γ2 mrg. inv mrg. exists nil. exists nil...
  move=>Δ σ Γ s A agr ih Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (A.[σ] :U G1).
    exists (A.[σ] :U G2)... }
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (A.[σ] :L G1).
    exists (_: G2)... }
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (_: G1).
    exists (A.[σ] :L G2)... }
  move=>Δ σ Γ agr ih Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    exists (_: G1).
    exists (_: G2)... }
  move=>Δ σ Γ n A agr ih tyn Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>{H2 ih}[G1[G2[mrg[agr1 agr2]]]].
    move:(merge_re_re mrg)=>[_[e1 e2]].
    exists G1.
    exists G2.
    repeat split...
    apply: agree_subst_wkU... by rewrite e1.
    apply: agree_subst_wkU... by rewrite e2. }
  move=>Δ1 Δ2 Δ σ Γ n A mrg agr ih tyn Γ1 Γ2 mrgL. inv mrgL.
  { move:(ih _ _ H2)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(merge_splitL mrg mrg1)=>[G3[mrg2 mrg3]].
    exists G3. exists G2... }
  { move:(ih _ _ H2)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(merge_splitR mrg mrg1)=>[G3[mrg2 mrg3]].
    exists G1. exists G3... }
  move=>Δ σ Γ n agr ih Γ1 Γ2 mrg. inv mrg.
  { move:(ih _ _ H2)=>[G1[G2[mrg1[agr1 agr2]]]].
    exists G1. exists G2... }
  move=>Δ σ Γ A B s l sb tyB1 tyB2 agr ih Γ1 Γ2 mrg. inv mrg.
  { have/ih[G1[G2[mrg[agr1 agr2]]]] : A :U Γ0 ∘ A :U Γ3 => A :U Γ...
    move:(merge_re_re mrg)=>[_[gd1 gd2]].
    move:(merge_re_re H2)=>[_[g0 g3]].
    exists G1. exists G2.
    repeat split...
    apply: agree_subst_conv...
    rewrite gd1...
    rewrite g0...
    apply: agree_subst_conv...
    rewrite gd2...
    rewrite g3... }
  { have/ih[G1[G2[mrg[agr1 agr2]]]] : A :L Γ0 ∘ _: Γ3 => A :L Γ...
    move:(merge_re_re mrg)=>[_[gd1 gd2]].
    move:(merge_re_re H2)=>[_[g0 g3]].
    exists G1. exists G2.
    repeat split...
    apply: agree_subst_conv...
    rewrite gd1...
    rewrite g0... }
  { have/ih[G1[G2[mrg[agr1 agr2]]]] : _: Γ0 ∘ A :L Γ3 => A :L Γ...
    move:(merge_re_re mrg)=>[_[gd1 gd2]].
    move:(merge_re_re H2)=>[_[g0 g3]].
    exists G1. exists G2.
    repeat split...
    apply: agree_subst_conv...
    rewrite gd2...
    rewrite g3... }
Qed.

Lemma esubstitution Γ m A Δ s σ :
  Γ ⊢ m : A : s -> Δ ⊢ σ ⊣ Γ -> Δ ⊢ m.[σ] : A.[σ] : s.
Proof with eauto using agree_subst, agree_subst_re, agree_subst_key.
  move=>ty. elim: ty Δ σ=>{Γ m A s}.
  move=>Γ s l k Δ σ agr. asimpl.
  { apply: clc_axiom... }
  move=>Γ A B s r t i k tyA ihA tyB ihB Δ σ agr. asimpl.
  { apply: clc_pi... }
  move=>Γ x A s hs Δ σ agr. asimpl.
  { apply: agree_subst_has... }
  move=>Γ A B m s r t i k tyP ihP tym ihm Δ σ agr. asimpl.
  { apply: clc_lam... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn Δ σ agr. asimpl.
  { move:(merge_agree_subst_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    move:(agree_subst_key agr2 k)=>{}k.
    apply: clc_app... }
  move=>Γ k Δ σ agr. asimpl.
  { apply: clc_unit... }
  move=>Γ k Δ σ agr. asimpl.
  { apply: clc_it... }
  move=>Γ A B s r t i mrg k tyA ihA tyB ihB Δ σ agr. asimpl.
  { apply: clc_sigma... }
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg 
    tyS ihS tym ihm tyn ihn Δ σ agr. asimpl.
  { move:(merge_agree_subst_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(agree_subst_key agr1 k1)=>{}k1.
    move:(agree_subst_key agr2 k2)=>{}k2.
    apply: clc_pair...
    move:(ihn _ _ agr2).
    by asimpl. }
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn ihn Δ σ agr. asimpl.
  { move:(merge_agree_subst_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    apply: clc_letin1... }
  move=>Γ1 Γ2 Γ A B C m n s r t k x i leq key mrg
    tym ihm tyC ihC tyn ihn Δ σ agr. asimpl.
  { move:(merge_agree_subst_inv agr mrg)=>[G1[G2[mrg1[agr1 agr2]]]].
    move:(ihm _ _ agr1)=>{ihm}tym.
    move:(agree_subst_key agr1 key)=>{}key.
    have/ihn{ihn}tyn: B.[up σ] :{r} A.[σ] :{s} G2 ⊢ up (up σ) ⊣
      B :{r} A :{s} Γ2...
    destruct k.
    have/ihC{ihC}tyC:(Sigma A B s r t).[σ] :U [G2] ⊢ up σ ⊣
      [Sigma A B s r t :U Γ2]...
    asimpl in tym.
    asimpl in tyC.
    replace C.[Pair (Var 1) (Var 0) t .: ren (+2)].[up (up σ)]
      with C.[up σ].[Pair (Var 1) (Var 0) t .: ren (+2)]
        in tyn by autosubst.
    have:=clc_letin2 leq key mrg1 tym tyC tyn.
    by asimpl.
    have/ihC{ihC}tyC:_: [G2] ⊢ up σ ⊣ [Sigma A B s r t :L Γ2]...
    asimpl in tym.
    asimpl in tyC.
    replace C.[Pair (Var 1) (Var 0) t .: ren (+2)].[up (up σ)]
      with C.[up σ].[Pair (Var 1) (Var 0) t .: ren (+2)]
        in tyn by autosubst.
    have:=clc_letin2 leq key mrg1 tym tyC tyn.
    by asimpl. }
  move=>Γ A B m s i sb tym ihm tyB ihB Δ σ agr.
  { apply: clc_conv.
    apply: sub_subst...
    apply: ihm...
    apply: ihB... }
Qed.

Lemma substitution Γ1 Γ2 Γ m n A B s t :
  A :{s} Γ1 ⊢ m : B : t ->
  Γ2 |> s ->
  Γ1 ∘ Γ2 => Γ -> 
  Γ2 ⊢ n : A : s -> 
  Γ ⊢ m.[n/] : B.[n/] : t.
Proof with eauto.
  move=>tym k mrg tyn.
  apply: esubstitution...
  destruct s.
  { apply: agree_subst_wkU.
    move:(merge_pureR mrg k)=>->...
    move:(merge_re_re mrg)=>[_[_<-]].
    rewrite<-pure_re...
    by asimpl. }
  { apply: agree_subst_wkL...
    by asimpl. }
Qed.

Lemma substitution2 Γ1 Γ2 Γ3 Γ4 Γ m1 m2 n A B C s r t :
  B :{r} A :{s} Γ1 ⊢ n : C : t->
  Γ2 |> s ->
  Γ3 |> r ->
  Γ1 ∘ Γ2 => Γ4 -> Γ3 ∘ Γ4 => Γ ->
  Γ2 ⊢ m1 : A : s ->
  Γ3 ⊢ m2 : B.[m1/] : r ->
  Γ ⊢ n.[m2,m1/] : C.[m2,m1/] : t.
Proof.
  move=>tyn k1 k2 mrg1 mrg2 ty1 ty2.
  apply: esubstitution.
  exact: tyn.
  move:(merge_re_re mrg1)=>[e0[e1 e2]].
  move:(merge_re_re mrg2)=>[e3[e4 e5]].
  destruct r; destruct s.
  { apply: agree_subst_wkU.
    apply: agree_subst_wkU.
    have e:=merge_pureR mrg1 k1; subst.
    have e:=merge_pureL mrg2 k2; subst.
    eauto. asimpl.
    rewrite<-e5. rewrite<-e2.
    by rewrite<-pure_re.
    rewrite<-e5. rewrite<-e3.
    by rewrite<-pure_re. }
  { have[G[mrg3 mrg4]]:=merge_splitR (merge_sym mrg2) mrg1. 
    apply: agree_subst_wkU.
    apply: agree_subst_wkL.
    exact: mrg4. eauto.
    have e:=merge_pureR mrg3 k2; subst.
    by asimpl.
    rewrite<-e4. by rewrite<-pure_re. }
  { have[G[mrg3 mrg4]]:=merge_splitR (merge_sym mrg2) mrg1. 
    apply: agree_subst_wkL.
    exact: mrg4.
    apply: agree_subst_wkU.
    eauto. asimpl.
    rewrite e0. by rewrite<-pure_re.
    have e:=merge_pureL mrg3 k1; subst.
    eauto. }
  { apply: agree_subst_wkL.
    apply: merge_sym.
    exact: mrg2.
    apply: agree_subst_wkL; eauto.
    by asimpl.
    eauto. }
Qed.

Lemma substitutionN Γ1 Γ2 m n A B s t :
  _: Γ1 ⊢ m : B : s -> Γ2 ⊢ n : A : t -> Γ1 ⊢ m.[n/] : B.[n/] : s.
Proof with eauto.
  move=>tym tyn.
  apply: esubstitution...
  apply: agree_subst_wkN...
Qed.

Lemma strengthen Γ m A s :
  _: Γ ⊢ m.[ren (+1)] : A.[ren (+1)] : s -> Γ ⊢ m : A : s.
Proof with eauto using key.
  move=>tym.
  have ty : (nil ⊢ U @ 0 : U @ 1 : U).
  apply: clc_axiom...
  have := (substitutionN tym ty).
  by asimpl.
Qed.

Lemma context_conv Γ m A B C s t l :
  B === A -> 
  [Γ] ⊢ A : s @ l : U -> A :{s} Γ ⊢ m : C : t -> B :{s} Γ ⊢ m : C : t.
Proof with eauto.
  move=>conv tpA tpm.
  cut (B :{s} Γ ⊢ m.[ids] : C.[ids] : t). autosubst.
  apply: esubstitution...
  apply: agree_subst_conv.
  apply: conv_sub...
  destruct s=>//=; asimpl.
  apply: eweakeningU; eauto.
  asimpl; eauto.
  apply: eweakeningN; eauto.
  asimpl; eauto.
  eauto.
  apply: agree_subst_refl.
Qed.