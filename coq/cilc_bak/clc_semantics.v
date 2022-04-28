From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine clc_respine clc_iota_lemma
  clc_resolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive eval : context term -> term -> context term -> term -> Prop :=
| eval_sort Θ s i l :
  l = length Θ ->
  eval Θ (Sort s i) (Sort s i :U Θ) (Ptr l)
| eval_pi Θ A B s r t l :
  l = length Θ ->
  eval Θ (Pi A B s r t) (Pi A B s r t :U Θ) (Ptr l)
| eval_lam Θ A m s t l :
  l = length Θ ->
  eval Θ (Lam A m s t) (Lam A m s t :{t} Θ) (Ptr l)
| eval_appL Θ Θ' m m' n :
  eval Θ m Θ' m' ->
  eval Θ (App m n) Θ' (App m' n)
| eval_appR Θ Θ' l n n' :
  eval Θ n Θ' n' ->
  eval Θ (App (Ptr l) n) Θ' (App (Ptr l) n')
| eval_beta Θ Θ' l1 l2 A m s t :
  free Θ l1 (Lam A m s t) Θ' ->
  eval Θ (App (Ptr l1) (Ptr l2)) Θ' m.[Ptr l2/]
| eval_indd Θ l A Cs s :
  l = length Θ ->
  eval Θ (Ind A Cs s) (Ind A Cs s :U Θ) (Ptr l)
| eval_appI Θ Θ' l1 l2 l A Cs s ms :
  l = length Θ ->
  free Θ l1 (spine (Ind A Cs s) ms) Θ' ->
  eval 
    Θ (App (Ptr l1) (Ptr l2)) 
    (spine (Ind A Cs s) (rcons ms (Ptr l2)) :U Θ') (Ptr l)
| eval_constr Θ l i I s :
  l = length Θ ->
  eval Θ (Constr i I s) (Constr i I s :{s} Θ) (Ptr l)
| eval_appC Θ Θ' l1 l2 l i I s ms :
  l = length Θ ->
  free Θ l1 (spine (Constr i I s) ms) Θ' ->
  eval
    Θ (App (Ptr l1) (Ptr l2))
    (spine (Constr i I s) (rcons ms (Ptr l2)) :{s} Θ') (Ptr l)
| eval_case Θ Θ' m m' Q Fs :
  eval Θ m Θ' m' ->
  eval Θ (Case m Q Fs) Θ' (Case m' Q Fs)
| eval_iota1 Θ Θ' l i I s ms Q Fs F :
  iget i Fs F ->
  free Θ l (spine (Constr i I s) ms) Θ' ->
  eval Θ (Case (Ptr l) Q Fs) Θ' (spine F ms)
| step_fix Θ l A m :
  l = length Θ ->
  eval Θ (Fix A m) (Fix A m :U Θ) m.[Ptr l/].

  Inductive agree_resolve :
  context term -> context term -> 
    (var -> term) -> (var -> term) -> nat -> Prop :=
| agree_resolve_nil Θ :
  Θ |> U ->
  wr_heap Θ ->
  agree_resolve nil Θ ids ids 0
| agree_resolve_upTy Γ Θ σ σ' A x s :
  agree_resolve Γ Θ σ σ' x ->
  agree_resolve (A :{s} Γ) Θ (up σ) (up σ') x.+1
| agree_resolve_upN Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x ->
  agree_resolve (_: Γ) Θ (up σ) (up σ') x.+1
| agree_resolve_wkU Γ Θ1 Θ2 Θ σ σ' m m' A :
  Θ1 ∘ Θ2 => Θ ->
  Θ2 |> U ->
  wr_heap Θ2 ->
  resolve Θ2 m m' ->
  agree_resolve Γ Θ1 σ σ' 0 ->
  agree_resolve (A :U Γ) Θ (m .: σ) (m' .: σ') 0
| agree_resolve_wkL Γ Θ1 Θ2 Θ σ σ' m m' A :
  Θ1 ∘ Θ2 => Θ ->
  wr_heap Θ2 ->
  resolve Θ2 m m' ->
  agree_resolve Γ Θ1 σ σ' 0 ->
  agree_resolve (A :L Γ) Θ (m .: σ) (m' .: σ') 0
| agree_resolve_wkN Γ Θ σ σ' m m' :
  agree_resolve Γ Θ σ σ' 0 ->
  agree_resolve (_: Γ) Θ (m .: σ) (m' .: σ') 0.

Lemma agree_resolve_key Γ Θ σ σ' x s :
  agree_resolve Γ Θ σ σ' x -> Γ |> s -> Θ |> s.
Proof.
  elim=>//{Γ Θ σ σ' x}.
  move=>Θ k1 wr k2. destruct s; eauto. apply: key_impure.
  move=>Γ Θ σ σ' A x t agr ih k. inv k; eauto.
  move=>Γ Θ σ σ' x agr ih k. inv k; eauto.
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k1 wr rsm agr ih k2. inv k2.
    apply: merge_pure_pure; eauto.
    apply: key_impure.
  move=>Γ Θ1 Θ2 Θ σ1 σ2 m m' A mrg wr rsm agr ih k. inv k.
    apply: key_impure.
  move=>Γ Θ σ1 σ2 m m' agr ih k. inv k; eauto.
Qed.

Lemma nf_agree_resolve_var Γ Θ σ σ' i x :
  agree_resolve Γ Θ σ σ' i -> x < i -> Var x = σ x.
Proof.
  move=>agr. elim: agr x=>//{Γ Θ σ σ' i}.
  move=>Γ Θ σ σ' A x s agr ih [|i] le//.
  asimpl.
  have/ih<-//:i < x by eauto.
  move=>Γ Θ σ σ' x agr ih [|i] le//.
  asimpl.
  have/ih<-//:i < x by eauto.
Qed.

Lemma nf_agree_resolve Γ Θ σ σ' i j m :
  nf i m -> i <= j -> agree_resolve Γ Θ σ σ' j -> m = m.[σ].
Proof with eauto using agree_resolve.
  move=>nf. move: i m nf Γ Θ σ σ' j.
  apply: nf_ind_nested...
  move=>i x lt Γ Θ σ σ' j leq agr.
  { apply: nf_agree_resolve_var; eauto.
    apply: leq_trans; eauto. }
  move=>i A B s r t nfA ihA nfB ihB Γ Θ σ σ' j leq agr.
  { have lt : i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: leq. exact: agr.
    apply: ihB. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
  move=>i A m s t nfA ihA nfm ihm Γ Θ σ σ' j leq agr.
  { have lt : i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: leq. exact: agr.
    apply: ihm. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
  move=>i m n nfm ihm nfn ihn Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihm; eauto.
    apply: ihn; eauto. }
  move=>i A Cs s nfA ihA nfCs ihCs Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihA; eauto.
    elim: ihCs=>{Cs nfCs}...
    move=>C Cs hd ih tl.
    asimpl. f_equal...
    have lt : i < j.+1 by eauto.
    apply: hd. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
  move=>i x I s nfI ihI Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihI; eauto. }
  move=>i m Q Fs nfm ihm nfQ ihQ nfFs ihFs Γ Θ σ σ' j leq agr.
  { asimpl. f_equal.
    apply: ihm; eauto.
    apply: ihQ; eauto.
    elim: ihFs=>{Fs nfFs}...
    move=>F Fs hd ih tl.
    asimpl. f_equal... }
  move=>i A m nfA ihA nfm ihm Γ Θ σ σ' j leq agr.
  { have lt : i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA; eauto.
    apply: ihm. exact: lt.
    apply: agree_resolve_upN. exact: agr. }
Qed.

Lemma agree_resolve_wr Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x -> wr_heap Θ.
Proof with eauto using wr_heap.
  elim=>{Γ Θ σ σ' x}...
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k wr2 rsm agr wr1.
  apply: wr_merge; eauto.
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr2 rsm agr wr1.
  apply: wr_merge; eauto.
Qed.

Definition id_ren i ξ := forall x, x < i -> ξ x = x.

Lemma id_ren1 : id_ren 0 (+1).
Proof. move=>x h. inv h. Qed.

Lemma id_ren_up i ξ : id_ren i ξ -> id_ren i.+1 (upren ξ).
Proof.
  move=>idr x h.
  destruct x.
  asimpl. eauto.
  asimpl. rewrite idr; eauto.
Qed.

Lemma nf_id_ren i m ξ : nf i m -> id_ren i ξ -> m = m.[ren ξ].
Proof.
  move=>nf. move: i m nf ξ.
  apply: nf_ind_nested=>//.
  move=>i x lt ξ idr.
  { asimpl. rewrite idr; eauto. }
  move=>i A B s r t nfA ihA nfB ihB ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihB; eauto.
    apply: id_ren_up; eauto. }
  move=>i A m s t nfA ihA nfm ihm ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihm; eauto.
    apply: id_ren_up; eauto. }
  move=>i m n nfm ihm nfn ihn ξ idr.
  { asimpl.
    rewrite<-ihm; eauto.
    rewrite<-ihn; eauto. }
  move=>i A Cs s nfA ihA nfCs ihCs ξ idr.
  { asimpl. f_equal.
    rewrite<-ihA; eauto.
    elim: ihCs=>//{Cs nfCs}.
    move=>C Cs ih hd tl.
    asimpl. f_equal; eauto.
    apply: ih.
    apply: id_ren_up; eauto. }
  move=>i x I s nfI ihI ξ idr.
  { asimpl. f_equal.
    rewrite<-ihI; eauto. }
  move=>i m Q Fs nfm ihm nfQ ihQ nfFs ihFs ξ idr.
  { asimpl. f_equal.
    rewrite<-ihm; eauto.
    rewrite<-ihQ; eauto.
    elim: ihFs=>//{Fs nfFs}.
    move=>F Fs ih hd tl.
    asimpl. f_equal; eauto. }
  move=>i A m nfA ihA nfm ihm ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihm; eauto.
    apply: id_ren_up; eauto. }
Qed.

Lemma ind_head_ren_inv m ξ : ind_head m.[ren ξ] -> ind_head m.
Proof.
  elim: m ξ=>//.
  move=>x ξ h. inv h. exfalso. solve_spine.
  move=>A ihA B ihB s r t ξ h. inv h. exfalso. solve_spine.
  move=>A ihA m ihm s t ξ h. inv h. exfalso. solve_spine.
  move=>m ihm n ihn ξ h. inv h. 
  { have[ms'[e1 e2]]:=ind_spine_app_inv H0; subst.
    have/ihm{}ihm: ind_head m.[ren ξ].
    { rewrite<-e1.
      constructor. }
    inv ihm.
    rewrite spine_app_rcons.
    constructor. }
  move=>A ihA Cs s ξ h.
  { replace (Ind A Cs s) with (spine (Ind A Cs s) nil) by eauto.
    constructor. }
  move=>i m ihm s ξ h. inv h. exfalso. solve_spine.
  move=>m ihm Q ihQ Fs ξ h. inv h. exfalso. solve_spine.
  move=>A ihA m ihm ξ h. inv h. exfalso. solve_spine.
Qed.

Lemma resolve_ren Θ m m' i ξ :
  resolve Θ m m' -> wr_heap Θ ->
  id_ren i ξ -> resolve Θ m.[ren ξ] m'.[ren ξ].
Proof with eauto using resolve, All2.
  move=>rs. move: Θ m m' rs i ξ.
  apply: resolve_ind_nested...
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i ξ wr idr.
  { asimpl.
    econstructor...
    apply: ihB...
    apply: id_ren_up... }
  move=>Θ A A' m m' s t k rsA ihA rsm ihm i ξ wr idr.
  { asimpl.
    econstructor...
    apply: ihA...
    apply: wr_heap_re...
    apply: ihm...
    apply: id_ren_up... }
  move=>Θ1 Θ2 Θ m m' n n' mrg h rm ihm rn ihn i ξ wr idr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor...
    move=>/ind_head_ren_inv/h//. }
  move=>Θ A A' Cs Cs' s k rA ihA rCs ihCs i ξ wr idr.
  { asimpl.
    econstructor...
    elim: ihCs=>{Cs Cs' rCs}...
    move=>C C' Cs Cs' ih hd tl.
    asimpl.
    constructor...
    apply: ih...
    apply: id_ren_up... }
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg rm ihm rQ ihQ rFs ihFs i ξ wr idr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor...
    apply: ihQ...
    apply: wr_heap_re...
    elim: ihFs=>{Fs Fs' rFs}... }
  move=>Θ A A' m m' k rA ihA rm ihm i ξ wr idr.
  { asimpl.
    econstructor...
    apply: ihm...
    apply: id_ren_up... }
  move=>Θ Θ' l m m' fr rm ihm i ξ wr idr.
  { asimpl.
    have nf0:=free_wr_nf fr wr.
    have {}wr:=free_wr fr wr.
    have nf0':=resolve_wr_nfi' rm wr nf0.
    have leq : 0 <= i by eauto.
    have nfi:=nf_weaken nf0' leq.
    have<-:=nf_id_ren nfi idr.
    econstructor... }
Qed.

Lemma agree_resolve_id Γ Θ σ σ' x i s A :
  agree_resolve Γ Θ σ σ' i -> has Γ x s A -> resolve Θ (σ x) (σ' x).
Proof with eauto using resolve.
  move=>agr. elim: agr x s A=>{Γ Θ σ σ' i}.
  move=>Θ k wr x s A hs. inv hs.
  move=>Γ Θ σ σ' A x s agr ih y t B hs.
  { inv hs; asimpl.
    constructor.
    apply: agree_resolve_key...
    apply: resolve_ren...
    apply: agree_resolve_wr...
    apply: id_ren1. }
  move=>Γ Θ σ σ' x agr ih y s A hs.
  { inv hs; asimpl.
    apply: resolve_ren...
    apply: agree_resolve_wr...
    apply: id_ren1. }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k2 wr rsm agr ih x s B hs.
  { inv hs; asimpl.
    have k1:=agree_resolve_key agr H5.
    have[e1 e2]:=merge_pure_eq mrg k1 k2.
    subst...
    have->:=merge_pureR mrg k2... }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr rsm agr ih x s B hs.
  { inv hs; asimpl.
    have k:=agree_resolve_key agr H5.
    have->:=merge_pureL mrg k... }
  move=>Γ Θ σ σ' m m' agr ih x s A hs.
  { inv hs; asimpl; eauto. }
Qed.

Lemma agree_resolve_re Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x -> agree_resolve [Γ] [Θ] σ σ' x.
Proof with eauto using agree_resolve.
  elim=>//={Γ Θ σ σ' x}...
  move=>Θ k wr. 
  { constructor. 
    apply: re_pure.
    apply: wr_heap_re... }
  move=>Γ Θ σ σ' A x [|]/= agr1 agr2...
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k wr rsm agr1 agr2.
  { econstructor.
    apply: merge_re3...
    apply: re_pure.
    apply: wr_heap_re...
    rewrite<-pure_re; eauto.
    exact: agr2. }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr rsm agr1 agr2.
  { have[e1[e2 e3]]:=merge_re_re mrg.
    econstructor.
    rewrite<-e2=>//. }
Qed.

Lemma agree_resolve_merge_inv Γ1 Γ2 Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x ->
  Γ1 ∘ Γ2 => Γ ->
  exists Θ1 Θ2,
    Θ1 ∘ Θ2 => Θ /\
    agree_resolve Γ1 Θ1 σ σ' x /\
    agree_resolve Γ2 Θ2 σ σ' x.
Proof with eauto using merge, agree_resolve.
  move=>agr. elim: agr Γ1 Γ2=>{Γ Θ σ σ' x}.
  move=>Θ k wr Γ1 Γ2 mrg.
  { inv mrg. 
    have[G1[G2[k1[k2 mrg]]]]:=pure_split k.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    exists G1. exists G2... }
  move=>Γ Θ σ σ' A x s agr ih Γ1 Γ2 mrg.
  { destruct s; inv mrg.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2...
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2...
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2... }
  move=>Γ Θ σ σ' x agr ih Γ1 Γ2 mrg.
  { inv mrg.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2... }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg1 k wr rsm agr ih Γ1 Γ2 mrg2.
  { inv mrg2.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    have e:=merge_pureR mrg1 k; subst.
    have mrgr:=merge_re_id Θ2.
    rewrite<-pure_re in mrgr...
    have[G1[G2[mrg3[mrg4 mrg5]]]]:=merge_distr mrg1 mrg' mrgr.
    exists G1. exists G2.
    repeat split... }
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg1 wr rsm agr ih Γ1 Γ2 mrg2.
  { inv mrg2.
    { have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      have[G[mrg3 mrg4]]:=merge_splitL mrg1 mrg'.
      exists G. exists D2.
      repeat split... } 
    { have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      have[G[mrg3 mrg4]]:=merge_splitR mrg1 mrg'.
      exists D1. exists G.
      repeat split... } }
  move=>Γ Θ σ σ' m m' agr ih Γ1 Γ2 mrg.
  { inv mrg.
    have[D1[D2[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists D1. exists D2.
    repeat split... }
Qed.

Lemma resolve_subst Γ Θ1 Θ2 Θ m m' A r σ σ' x :
  Γ ⊢ m' : A : r -> Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' -> wr_heap Θ1 ->
  agree_resolve Γ Θ2 σ σ' x ->
  resolve Θ m.[σ] m'.[σ'].
Proof with eauto using resolve, merge_pure_pure.