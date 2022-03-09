From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_linearity clc_resolution.

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
| eval_beta Θ Θ' lf la A m s t :
  free Θ lf (Lam A m s t) Θ' ->
  eval Θ (App (Ptr lf) (Ptr la)) Θ' m.[Ptr la/]
| eval_unit Θ l :
  l = length Θ ->
  eval Θ Unit (Unit :U Θ) (Ptr l)
| eval_it Θ l :
  l = length Θ ->
  eval Θ It (It :U Θ) (Ptr l)
| eval_sigma Θ A B s r t l :
  l = length Θ ->
  eval Θ (Sigma A B s r t) (Sigma A B s r t :U Θ) (Ptr l)
| eval_pairL Θ Θ' m m' n t :
  eval Θ m Θ' m' ->
  eval Θ (Pair m n t) Θ' (Pair m' n t)
| eval_pairR Θ Θ' l n n' t :
  eval Θ n Θ' n' ->
  eval Θ (Pair (Ptr l) n t) Θ' (Pair (Ptr l) n' t)
| eval_pairV Θ l lm ln t :
  l = length Θ ->
  eval Θ (Pair (Ptr lm) (Ptr ln) t)
         ((Pair (Ptr lm) (Ptr ln) t) :{t} Θ) (Ptr l)
| eval_letin1 Θ Θ' m m' n :
  eval Θ m Θ' m' ->
  eval Θ (LetIn1 m n) Θ' (LetIn1 m' n)
| eval_iota1 Θ Θ' l n :
  free Θ l It Θ' ->
  eval Θ (LetIn1 (Ptr l) n) Θ' n
| eval_iota2 Θ Θ' lm ln l n t :
  free Θ l (Pair (Ptr lm) (Ptr ln) t) Θ' ->
  eval Θ (LetIn2 (Ptr l) n) Θ' n.[Ptr ln,Ptr ln/].

Inductive agree_resolve :
  context term -> context term -> 
    (var -> term) -> (var -> term) -> nat -> Prop :=
| agree_resolve_nil :
  agree_resolve nil nil ids ids 0

| agree_resolve_upTy Γ Θ σ σ' A x s :
  agree_resolve Γ Θ σ σ' x ->
  agree_resolve (A :{s} Γ) Θ (up σ) (up σ') x.+1

| agree_resolve_upN Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x ->
  agree_resolve (_: Γ) Θ (up σ) (up σ') x.+1

| agree_resolve_wkU Γ Θ1 Θ2 Θ σ σ' m m' A :
  Θ1 ∘ Θ2 => Θ ->
  Θ2 |> U ->
  wr_env Θ2 ->
  resolve Θ2 m m' ->
  agree_resolve Γ Θ1 σ σ' 0 ->
  agree_resolve (A :U Γ) Θ (m .: σ) (m' .: σ') 0

| agree_resolve_wkL Γ Θ1 Θ2 Θ σ σ' m m' A :
  Θ1 ∘ Θ2 => Θ ->
  wr_env Θ2 ->
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
  move=>Γ Θ σ σ' A x t agr ih k. inv k; eauto.
  move=>Γ Θ σ σ' x agr ih k. inv k; eauto.
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k1 wr rsm agr ih k2. inv k2.
    apply: merge_pure_pure; eauto.
    apply: key_impure.
  move=>Γ Θ1 Θ2 Θ σ1 σ2 m m' A mrg wr rsm agr ih k. inv k.
    apply: key_impure.
  move=>Γ Θ σ1 σ2 m m' agr ih k. inv k; eauto.
Qed.

(* Lemma agree_resolve_free Γ Θ σ σ' Θ' x Θ1 l m :
  agree_resolve Γ Θ σ σ' Θ' x -> free Θ l m Θ1 -> 
    exists Θ2, free Θ' l m Θ2.
Proof.
  move=>agr. elim: agr l m Θ1=>//{Γ Θ σ σ' Θ' x}.
  move=>Γ Θ1 Θ2 Θ m m' A mrg k wr rs l m0 Θ0 fr.
  { have[G[fr' _]]:=free_merge fr mrg.
    exists G. exact: fr'. }
  move=>Γ Θ1 Θ2 Θ m m' A mrg wr rs l m0 Θ0 fr.
  { have[G[fr' _]]:=free_merge fr mrg.
    exists G. exact: fr'. }
Qed. *)

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
  move=>nf. elim: nf Γ Θ σ σ' j=>{i m}//.
  move=>i x le1 Γ Θ σ σ' j le2 agr.
    apply: nf_agree_resolve_var; eauto.
    apply: leq_trans; eauto.
  move=>i A B s r t nfA ihA nfB ihB Γ Θ σ σ' j le agr.
    have le1:i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: le. exact: agr.
    apply: ihB. exact: le1. 
    apply: agree_resolve_upN. exact: agr.
  move=>i A m s t nfA ihA nfm ihm Γ Θ σ σ' j le agr.
    have le1:i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: le. exact: agr.
    apply: ihm. exact: le1. 
    apply: agree_resolve_upN. exact: agr.
  move=>i m n nfm ihm nfn ihn Γ Θ σ σ' j le agr.
    asimpl. f_equal.
    apply: ihm. exact: le. exact: agr.
    apply: ihn. exact: le. exact: agr.
  move=>i A B s r t nfA ihA nfB ihB Γ Θ σ σ' j le agr.
    have le1:i < j.+1 by eauto. asimpl. f_equal.
    apply: ihA. exact: le. exact: agr.
    apply: ihB. exact: le1. 
    apply: agree_resolve_upN. exact: agr.
  move=>i m n t nfm ihm nfn ihn Γ Θ σ σ' j le agr.
    asimpl. f_equal.
    apply: ihm. exact: le. exact: agr.
    apply: ihn. exact: le. exact: agr.
  move=>i m n nfm ihm nfn ihn Γ Θ σ σ' j le agr.
    asimpl. f_equal.
    apply: ihm. exact: le. exact: agr.
    apply: ihn. exact: le. exact: agr.
  move=>i m n nfm ihm nfn ihn Γ Θ σ σ' j le agr.
    have le1:i.+1 < j.+2 by eauto. asimpl. f_equal.
    apply: ihm. exact: le. exact: agr.
    have{}agr:=agree_resolve_upN agr.
    have{}agr:=agree_resolve_upN agr.
    have{}ihn:=ihn (_: _: Γ) Θ (up (up σ)) (up (up σ')) _ le1 agr.
    asimpl in ihn.
    apply: ihn.
Qed.

Lemma agree_resolve_wr Γ Θ σ σ' x :
  agree_resolve Γ Θ σ σ' x -> wr_env Θ.
Proof with eauto using wr_env.
  elim=>{Γ Θ σ σ' x}...
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k wr2 rsm agr wr1.
  apply: wr_merge; eauto.
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg wr2 rsm agr wr1.
  apply: wr_merge; eauto.
Qed.

Definition id_ren i ξ := forall x, x < i -> ξ x = x.

Lemma id_ren1 : id_ren 0 (+1).
Proof.
  move=>x h. inv h.
Qed.

Lemma id_ren_up i ξ : id_ren i ξ -> id_ren i.+1 (upren ξ).
Proof.
  move=>idr x h.
  destruct x.
  asimpl. eauto.
  asimpl. rewrite idr; eauto.
Qed.

Lemma nf_id_ren i m ξ : nf i m -> id_ren i ξ -> m = m.[ren ξ].
Proof.
  move=>nf. elim: nf ξ=>//={i m}.
  move=>i x le ξ idr.
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
  { rewrite<-ihm; eauto.
    rewrite<-ihn; eauto. }
  move=>i A B s r t nfA ihA nfB ihB ξ idr.
  { asimpl.
    rewrite<-ihA; eauto.
    rewrite<-ihB; eauto.
    apply: id_ren_up; eauto. }
  move=>i m n t nfm ihm nfn ihn ξ idr.
  { rewrite<-ihm; eauto.
    rewrite<-ihn; eauto. }
  move=>i m n nfm ihm nfn ihn ξ idr.
  { rewrite<-ihm; eauto.
    rewrite<-ihn; eauto. }
  move=>i m n nfm ihm nfn ihn ξ idr.
  { replace (upn 2 (ren ξ)) with
      (ren (upren (upren ξ))) by autosubst.
    rewrite<-ihm; eauto.
    rewrite<-ihn; eauto. 
    apply: id_ren_up.
    apply: id_ren_up; eauto. }
Qed.

Lemma resolve_ren Θ m m' i ξ :
  resolve Θ m m' -> wr_env Θ -> 
    id_ren i ξ -> resolve Θ m.[ren ξ] m'.[ren ξ].
Proof with eauto using resolve.
  move=>rs. elim: rs i ξ=>//{Θ m m'}...
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i ξ wr idr.
  { asimpl.
    econstructor; eauto.
    apply: ihB; eauto.
    apply: id_ren_up; eauto. }
  move=>Θ A A' m m' s t k rsA ihA rsm ihm i ξ wr idr.
  { asimpl.
    econstructor; eauto.
    apply: ihA; eauto.
    apply: wr_env_re; eauto.
    apply: ihm; eauto.
    apply: id_ren_up; eauto. }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i ξ wr idr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor; eauto. }
  move=>Θ A A' B B' s r t k rsA ihA rsB ihB i ξ wr idr.
  { asimpl.
    econstructor; eauto.
    apply: ihB; eauto.
    apply: id_ren_up; eauto. }
  move=>Θ1 Θ2 Θ m m' n n' t k mrg rsm ihm rsn ihn i ξ wr dr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor; eauto. }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i ξ wr idr.
  { asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor; eauto. }
  move=>Θ1 Θ2 Θ m m' n n' mrg rsm ihm rsn ihn i ξ wr idr.
  { replace (LetIn2 m n).[ren ξ] 
      with (LetIn2 m.[ren ξ] n.[ren (upren (upren ξ))])
        by autosubst.
    replace (LetIn2 m' n').[ren ξ] 
      with (LetIn2 m'.[ren ξ] n'.[ren (upren (upren ξ))])
        by autosubst.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    econstructor; eauto.
    apply: ihn; eauto.
    apply: id_ren_up.
    apply: id_ren_up; eauto. }
  move=>Θ Θ' l m m' fr rm ih i ξ wr idr.
  { asimpl.
    have nf0:=free_wr_nf fr wr.
    have {}wr:=free_wr fr wr.
    have nf0':=resolve_wr_nfi' rm wr nf0.
    have le:0 <= i by eauto.
    have nfi:=nf_weaken nf0' le.
    have <-:=nf_id_ren nfi idr.
    econstructor; eauto. }
Qed.

Lemma agree_resolve_id Γ Θ σ σ' x i s A :
  agree_resolve Γ Θ σ σ' i -> has Γ x s A -> resolve Θ (σ x) (σ' x).
Proof with eauto using resolve.
  move=>agr. elim: agr x s A=>{Γ Θ σ σ' i}.
  move=>x s A hs. inv hs.
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
  move=>Γ Θ σ σ' A x [|]/= agr1 agr2...
  move=>Γ Θ1 Θ2 Θ σ σ' m m' A mrg k wr rsm agr1 agr2.
  { econstructor.
    apply: merge_re3...
    apply: re_pure.
    apply: wr_env_re...
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
  move=>Γ1 Γ2 mrg.
  { inv mrg. exists nil. exists nil... }
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
  resolve Θ1 m m' -> wr_env Θ1 ->
  agree_resolve Γ Θ2 σ σ' x ->
  resolve Θ m.[σ] m'.[σ'].
Proof with eauto using resolve, merge_pure_pure.
  move=>ty. elim: ty Θ1 Θ2 Θ m σ σ' x=>{Γ m' A r}.
  move=>Γ s l k Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k2:=agree_resolve_key agr k.
      econstructor... }
    { destruct m0; inv H0.  
      have e:=free_wr_sort H wr; subst.
      have p:=agree_resolve_key agr k.
      have[e1 e2]:=merge_pure_eq mrg H3 p; subst.
      econstructor...
      exfalso. apply: free_wr_ptr; eauto. } }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { constructor.
      have k2:=agree_resolve_key agr k...
      apply: ihA...
      have ag1:agree_resolve (A :U [Γ]) Θ2 (up σ) (up σ') x.+1. 
        apply: agree_resolve_upTy; eauto.
        rewrite<-pure_re; eauto.
      have ag2:agree_resolve (_: [Γ]) Θ2 (up σ) (up σ') x.+1.
        apply: agree_resolve_upN.
        rewrite<-pure_re; eauto. 
      apply: ihB...
      destruct s... }
    { destruct m0; inv H0.
      have nfP:=free_wr_nf H wr.
      have e:=free_wr_pi H wr; subst.
      have k1:=agree_resolve_key agr k.
      have[e1 e2]:=merge_pure_eq mrg H5 k1; subst.
      inv nfP.
      econstructor...
      econstructor...
      have le1:0 <= x by eauto.
      have->:=nf_agree_resolve H3 le1 agr.
      apply: ihA...
      have le2:0 < x.+1 by eauto.
      destruct s.
      { have agr': agree_resolve (A :U [Γ]) Θ (up σ) (up σ') x.+1.
          apply: agree_resolve_upTy.
          rewrite<-pure_re...
        have->:=nf_agree_resolve H8 le2 agr'... }
      { have agr': agree_resolve (_: [Γ]) Θ (up σ) (up σ') x.+1.
          apply: agree_resolve_upN.
          rewrite<-pure_re...
        have->:=nf_agree_resolve H8 le2 agr'... }
      exfalso. apply: free_wr_ptr; eauto. } }
  move=>Γ x A s hs Θ1 Θ2 Θ m σ σ' x0 mrg rsm wr agr.
  { inv rsm; asimpl.
    { have e:=merge_pureL mrg H2; subst.
      apply: agree_resolve_id... }
    { destruct m0; inv H0.
      have//:=free_wr_var H wr.
      have//:=free_wr_ptr H wr. } }
  move=>Γ A B m s r t i k tyP ihP tym ihm Θ1 Θ2 Θ n σ σ' x mrg rsL wr agr.
  { have[lP[tyA[_ tyB]]]:=pi_inv _ _ _ _ _ _ _ _ tyP.
    inv rsL; asimpl.
    { econstructor.
      destruct t.
      have k2:=agree_resolve_key agr k...
      apply: key_impure.
      have rsP: resolve [Θ1] (Pi A0 B s r t) (Pi A B s r t).
        econstructor...
        apply: re_pure.
        apply: resolve_type_refl...
      have{}ihP:=ihP _ _ _ _ _ _ _ 
        (merge_re3 mrg) rsP (wr_env_re wr) (agree_resolve_re agr).
      inv ihP...
      apply: ihm...
      destruct s.
      { econstructor... }
      { econstructor... } }
    { destruct m0; inv H0.
      have nfL:=free_wr_nf H wr.
      have k2:=agree_resolve_key agr k.
      inv nfL.
      have[G[fr mrg']]:=free_merge H mrg.
      have wr':=free_wr H wr.
      econstructor...
      econstructor...
      apply: merge_key...
      have le1:0 <= x by eauto.
      have->:=nf_agree_resolve H3 le1 agr.
      have[e1[e2 e3]]:=merge_re_re mrg'.
      have rsP: resolve [Θ'] (Pi m0 B s r t) (Pi A B s r t).
        econstructor...
        apply: re_pure.
        apply: resolve_type_refl...
      have{}ihP:=ihP _ _ _ _ _ _ _ 
        (merge_re3 mrg') rsP (wr_env_re wr') (agree_resolve_re agr).
      inv ihP...
      have le2:0 < x.+1 by eauto.
      destruct s.
      { have agr': agree_resolve (A :U Γ) Θ2 (up σ) (up σ') x.+1.
          apply: agree_resolve_upTy...
        have->:=nf_agree_resolve H7 le2 agr'... }
      { have agr': agree_resolve (A :L Γ) Θ2 (up σ) (up σ') x.+1.
          apply: agree_resolve_upTy...
        have->:=nf_agree_resolve H7 le2 agr'... }
      exfalso. apply: free_wr_ptr; eauto. } }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg1 tym ihm tyn ihn 
    Θ1 Θ2 Θ m0 σ σ' x mrg2 rsm wr agr.
  { inv rsm; asimpl.
    { have[wr1 wr2]:=wr_merge_inv H1 wr.
      have[G1[G2[mrg5[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[D1[D2[mrg6[mrg7 mrg8]]]]:=merge_distr mrg2 H1 mrg5.
      econstructor.
      apply: mrg6.
      apply: ihm...
      apply: ihn... }
    { destruct m1; inv H0.
      have nfa:=free_wr_nf H wr.
      inv nfa.
      have[G[fr mrg']]:=free_merge H mrg2.
      have[G1[G2[mrg5[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[D1[D2[mrg6[mrg7 mrg8]]]]:=merge_distr mrg' H6 mrg5.
      have wr':=free_wr H wr.
      have[wr1 wr2]:=wr_merge_inv H6 wr'.
      have le:0 <= x by eauto.
      econstructor...
      econstructor.
      apply: mrg6.
      have->:=nf_agree_resolve H3 le agr1.
      apply:ihm...
      have->:=nf_agree_resolve H4 le agr2.
      apply:ihn...
      exfalso. apply: free_wr_ptr; eauto. } }
  move=>Γ k Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k':=agree_resolve_key agr k.
      econstructor... }
    { have k':=agree_resolve_key agr k.
      have e:=merge_pureR mrg k'; subst.
      econstructor... } }
  move=>Γ k Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { have k':=agree_resolve_key agr k.
      econstructor... }
    { have k':=agree_resolve_key agr k.
      have e:=merge_pureR mrg k'; subst.
      econstructor... } }
  move=>Γ A B s r t i le k tyA ihA tyB ihB 
    Θ1 Θ2 Θ m σ σ' x mrg rsm wr agr.
  { inv rsm; asimpl.
    { constructor.
      have k2:=agree_resolve_key agr k...
      apply: ihA...
      have ag1:agree_resolve (A :U [Γ]) Θ2 (up σ) (up σ') x.+1. 
        apply: agree_resolve_upTy; eauto.
        rewrite<-pure_re; eauto.
      have ag2:agree_resolve (_: [Γ]) Θ2 (up σ) (up σ') x.+1.
        apply: agree_resolve_upN.
        rewrite<-pure_re; eauto. 
      apply: ihB...
      destruct s... }
    { destruct m0; inv H0.
      have nfP:=free_wr_nf H wr.
      have e:=free_wr_sigma H wr; subst.
      have k1:=agree_resolve_key agr k.
      have[e1 e2]:=merge_pure_eq mrg H5 k1; subst.
      inv nfP.
      econstructor...
      econstructor...
      have le1:0 <= x by eauto.
      have->:=nf_agree_resolve H3 le1 agr.
      apply: ihA...
      have le2:0 < x.+1 by eauto.
      destruct s.
      { have agr': agree_resolve (A :U [Γ]) Θ (up σ) (up σ') x.+1.
          apply: agree_resolve_upTy.
          rewrite<-pure_re...
        have->:=nf_agree_resolve H8 le2 agr'... }
      { have agr': agree_resolve (_: [Γ]) Θ (up σ) (up σ') x.+1.
          apply: agree_resolve_upN.
          rewrite<-pure_re...
        have->:=nf_agree_resolve H8 le2 agr'... }
      exfalso. apply: free_wr_ptr; eauto. } }
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg1 tyS ihS tym ihm tyn ihn
    Θ1 Θ2 Θ m0 σ σ' x mrg2 rsm wr agr.
  { inv rsm; asimpl.
    { econstructor.
      
    
      have[wr1 wr2]:=wr_merge_inv H1 wr.
      have[G1[G2[mrg5[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[D1[D2[mrg6[mrg7 mrg8]]]]:=merge_distr mrg2 H1 mrg5.
      econstructor.
      apply: mrg6.
      apply: ihm...
      apply: ihn... }
    { destruct m1; inv H0.
      have nfa:=free_wr_nf H wr.
      inv nfa.
      have[G[fr mrg']]:=free_merge H mrg2.
      have[G1[G2[mrg5[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[D1[D2[mrg6[mrg7 mrg8]]]]:=merge_distr mrg' H6 mrg5.
      have wr':=free_wr H wr.
      have[wr1 wr2]:=wr_merge_inv H6 wr'.
      have le:0 <= x by eauto.
      econstructor...
      econstructor.
      apply: mrg6.
      have->:=nf_agree_resolve H3 le agr1.
      apply:ihm...
      have->:=nf_agree_resolve H4 le agr2.
      apply:ihn...
      exfalso. apply: free_wr_ptr; eauto. } }



      (* Lemma resolve_substL Θ1 Θ2 Θ m m' n n' A B r :
  A :L nil ⊢ m' : B : r -> 
  resolve Θ1 m m' -> resolve Θ2 n n' -> wr_env Θ ->
  merge Θ1 Θ2 Θ -> resolve Θ m.[n/] m'.[n'/].
Proof.
  intros.
  apply: resolve_subst.
  apply: H.
  apply: H0.
  admit.
  econstructor.
  apply: H3.
  econstructor.
  apply: H1.


  move e:(A :L nil)=>Γ ty. elim: ty A e Θ1 Θ2 Θ m n n'=>{Γ r m' B};
  intros; subst. 
  { inv H. }
  { inv H. }
  { destruct x. inv H.
    simpl.
    inv H0.
    simpl.
    have->//:=merge_pureL H3 H6.
    have[wr1 wr2]:=wr_merge_inv H3 H2.
    destruct m0; inv H4.
    exfalso.
    apply: free_wr_var.
    apply: H.
    apply: wr1.
    exfalso. apply: free_wr_ptr.
    apply: H.
    apply: wr1.
    inv H. }
  { inv H.
    destruct m0; inv H4.
    admit.
    asimpl.
    asimpl.
    econstructor.

  }
  admit. *)
  
Lemma eval_split Θ1 Θ2 Θ Θ' m n m' A t :
  well_resolved Θ1 m n A t -> wr_env Θ -> 
  Θ1 ∘ Θ2 => Θ -> eval Θ m Θ' m' ->
  exists Θ1' Θ2' n', 
    well_resolved Θ1' m' n' A t /\ wr_env Θ' /\
    pad Θ2 Θ2' /\ Θ1' ∘ Θ2' => Θ' /\ n ~>* n'.
Proof with eauto 6 using 
  clc_type, key, free, pad, merge, 
  well_resolved, resolve, resolve_wkU, resolve_wkN.
  move=>{Θ1 m n A t}[Θ1 m n A t rm]. move e:(nil)=>Γ tyn.
  elim: tyn Θ1 Θ2 Θ Θ' m m' rm e=>{Γ n A t}.
  move=>Γ s l k Θ1 Θ2 Θ Θ' m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev.
    exists ((s @ l) :U Θ1).
    exists ((s @ l) :U Θ2).
    exists (s @ l).
    repeat split...
    econstructor.
    move:mrg=>/merge_length[<-_]... 
    econstructor... 
    econstructor... }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ1 Θ2 Θ Θ' 
    m m' rsm e wr mrg ev; subst.
  { inv rsm; inv ev.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    exists ((Pi A0 B0 s r t) :U Θ1).
    exists ((Pi A0 B0 s r t) :U Θ2).
    exists (Pi A B s r t).
    repeat split...
    econstructor.
    move:mrg=>/merge_length[<-_]... 
    econstructor... 
    econstructor... 
    have//=nfA:=nf_typing tyA.
    have//:=resolve_wr_nfi H7 wr1 nfA.
    destruct s; simpl in tyB.
    have//=nfB:=nf_typing tyB.
    have//:=resolve_wr_nfi H8 wr1 nfB.
    have//=nfB:=nf_typing tyB.
    have//:=resolve_wr_nfi H8 wr1 nfB. }
  move=>Γ x A s hs Θ1 Θ2 Θ Θ' m m' rsm e tyA mrg ev.
  { inv rsm; inv ev. }
  move=>Γ A B m s r t i k tyP ihP tym ihm 
    Θ1 Θ2 Θ Θx n m' rsL e wr mrg ev.
  { inv rsL; inv ev.
    have[<-_]:=merge_length mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct t.
    { exists ((Lam A0 m0 s U) :U Θ1).
      exists ((Lam A0 m0 s U) :U Θ2).
      exists (Lam A m s U).
      repeat split... 
      econstructor... 
      have[l0[tyA[_ _]]]:=pi_inv _ _ _ _ _ _ _ _ tyP.
      have//=nfA:=nf_typing tyA.
      have//:=resolve_wr_nfi H6 (wr_env_re wr1) nfA.
      destruct s.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm. }
    { exists ((Lam A0 m0 s L) :L Θ1).
      exists (_: Θ2).
      exists (Lam A m s L).
      repeat split... 
      econstructor... 
      have[l0[tyA[_ _]]]:=pi_inv _ _ _ _ _ _ _ _ tyP.
      have//=nfA:=nf_typing tyA.
      have//:=resolve_wr_nfi H6 (wr_env_re wr1) nfA.
      destruct s.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm.
      have//=nfm:=nf_typing tym.
      have//:=resolve_wr_nfi H7 wr1 nfm. } }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg1 tym ihm tyn ihn
    Θ1 Θ2 Θ Θ' x x' rx e wf mrg2 ev; subst.
  { inv mrg1.
    have[l tyP]:= validity nil_ok tym.
    have[l0[tyA[_ tyB]]]:= pi_inv _ _ _ _ _ _ _ _ tyP.
    inv rx; inv ev.
    { have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have[Θx1[Θx2[mx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihm _ _ _ _ _ _ H4 erefl wf mrg4 H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App mx n).
      repeat split...
      econstructor.
      exact: (merge_sym mrp1).
      eauto.
      apply: resolve_pad...
      apply: red_app... }
    { have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H1.
      have{ihn}[Θx1[Θx2[nx[wr[wf'[pd[mrgx rx]]]]]]]:=
        ihn _ _ _ _ _ _ H5 erefl wf (merge_sym mrg4) H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      inv wr.
      exists Θy. exists Θ2p.
      exists (App m nx).
      repeat split...
      econstructor. 
      exact: mrp1.
      apply: resolve_pad... eauto.
      destruct s.
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have mrgs:[@nil (elem term)] ∘ nil => nil. simpl...
        have h:=substitution tyB k mrgs tyn... }
      { apply: clc_conv.
        apply: conv_sub.
        apply: conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: rx.
        apply: clc_app...
        have h:=substitutionN tyB tyn... }
      eauto.
      apply: red_app... } 
    { move=>{ihm ihn}.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have[G[mrg rs]]:=resolve_free H7 H4 mrg4.
      have[Gx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      exists Gx. exists Θ2. inv rs. exists (m'.[n/]).
      have tym':=lam_inv _ _ _ _ _ _ _ _ _ _ _ _ _ tyP tym.
      repeat split...
      have[wf1 wf2]:=wr_merge_inv mrg2 wf.
      have[wf0 wf3]:=wr_merge_inv H1 wf1.
      have vn:=wr_resolve_value wf3 H5.
      have key:=resolution tyn vn wf3 H5.
      destruct s.
      { admit. }
      { have os:of_sort (A :L nil) 0 (Some L) by constructor.
        have {}os:=linearity tym' os.

      }
      

      admit.
      apply: substitution...
      apply: free_wr...
      apply: star1.
      apply: step_beta. } }


  (* move=>Γ s l k wf Θ1 Θ2 Θ Θ' m m' A rsm rsA mrg ev.
  { inv rsm; inv ev.
    exists ((s @ l) :U Θ1).
    exists ((s @ l) :U Θ2).
    repeat split...
    move:mrg=>/merge_length[<-_].
    exists (s @ l). exists (U @ l.+1).
    repeat split... }
  move=>Γ A B s r t i k tyA ihA tyB ihB wf Θ1 Θ2 Θ Θ' m m' C
    rsm rsC mrg ev.
  { inv rsm; inv ev.
    exists ((Pi A0 B0 s t) :U Θ1).
    exists ((Pi A0 B0 s t) :U Θ2).
    repeat split...
    move:mrg=>/merge_length[<-_].
    exists (Pi A B s t). exists (t @ i).
    repeat split... }
  move=>Γ x A s hs wf Θ1 Θ2 Θ Θ' m m' C rsm rsC mrg ev.
  { inv rsm; inv ev. }
  move=>Γ A B m s t i k tyP ihP tym ihm wf Θ1 Θ2 Θ Θx n m' C
    rsL rsC mrg ev.
  { inv rsL; inv ev.
    have[<-_]:=merge_length mrg.
    destruct t.
    { exists ((Lam A0 m0 s U) :U Θ1).
      exists ((Lam A0 m0 s U) :U Θ2).
      repeat split...
      exists (Lam A m s U). exists (Pi A B s U).
      repeat split... }
    { exists ((Lam A0 m0 s L) :L Θ1).
      exists (_: Θ2).
      repeat split...
      exists (Lam A m s L). exists (Pi A B s L).
      repeat split... } }
  move=>Γ1 Γ2 Γ A B m n s t k mrg1 tym ihm tyn ihn
    wf Θ1 Θ2 Θ Θ' x x' C rx rC mrg2 ev.
  { have[wf1 wf2]:=merge_context_ok_inv mrg1 wf.
    have[r[l tyP]]:= validity wf1 tym.
    have[r0[l0[tyA tyB]]]:= pi_inv _ _ _ _ _ _ tyP.
    inv rx; inv ev.
    { have rP:=resolve_type_refl Θ0 tyP.
      have[Θx[mrg3 mrg4]]:=merge_splitR mrg2 H1.
      have{ihm}[Θx1[Θx2[wr[pd mrgx]]]]:=
        ihm wf1 _ _ _ _ _ _ _ H4 rP mrg4 H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      exists Θy. exists Θ2p.
      repeat split...
      move:wr=>[mx[tyPx[rx1[rx2 tyx]]]].
      exists (App mx n). exists (B.[n/]).
      repeat split.
      econstructor. exact: (merge_sym mrp1).
      exact: rx1. apply: resolve_pad...
      have[_[<-_]]:=merge_re_re mrp1.
      apply: resolve_pad.
      apply: pad_re...
      have[_[_->]]:=merge_re_re H1...
      have e:=resolve_type_id tyP rx2; subst.
      apply: clc_app... }
    { have rA:=resolve_type_refl Θ3 tyA.
      have[Θx[mrg3 mrg4]]:=merge_splitL mrg2 H1.
      have{ihn}[Θx1[Θx2[wr[pd mrgx]]]]:=
        ihn wf2 _ _ _ _ _ _ _ H5 rA (merge_sym mrg4) H7.
      have[Θ3p[Θ2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Θy[mrp1 mrp2]]:=merge_splitL (merge_sym mrgx) mrp.
      exists Θy. exists Θ2p.
      repeat split...
      move:wr=>[nx[tyPx[rx1[rx2 tyx]]]].
      exists (App m nx). exists (B.[nx/]).
      repeat split.
      econstructor. exact: mrp1.
      apply: resolve_pad... exact: rx1.
      have[_[<-_]]:=merge_re_re mrp1.
      apply: resolve_pad.
      apply: pad_re...
      have[_[->_]]:=merge_re_re H1...
      have:=eval_red _.
      admit.
      have e:=resolve_type_id tyA rx2; subst.
      apply: clc_app... }

  }
Admitted. *)

Lemma well_resolved_eval Θ Θ' Γ m m' A :
  well_resolved Θ Γ m A -> eval Θ m Θ' m' -> well_resolved Θ' Γ m' A.
Proof with eauto using 
  clc_type, resolve, resolve_wkU, resolve_wkN, free.
  move=>[n[B[rm[rA tyn]]]].
  elim: tyn Θ Θ' m m' A rm rA=>{Γ n B}.
  move=>Γ s l k Θ Θ' m m' A rsm rsA ev.
  { inv rsm. inv ev.
    exists (s @ l). exists (U @ l.+1).
    repeat split...
    inv ev. }
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ Θ' m m' C rs1 rs2 ev.
  { inv rs1. inv ev.
    exists (Pi A B s t). exists (t @ i).
    repeat split...
    inv ev. }
  move=>Γ x A s hs Θ Θ' m m' C rs1 rs2 ev.
  { inv rs1. inv ev. inv ev. }
  move=>Γ A B m s t i k tyP ihP tym ihm Θ Θ' rs n C rs1 rs2 ev.
  { inv rs1. inv ev.
    exists (Lam A m s t). exists (Pi A B s t).
    destruct t; repeat split...  
    inv ev. }
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn 
    Θ Θ' n' m' C rs1 rs2 ev.
  { inv rs1. inv ev.
    {
      (* { have[G1[G2[mx[rs'[pd mrg']]]]]:= *)
      have wr:well_resolved Θ1 Γ1 m0 (Pi A B s t).
      exists m. exists (Pi A B s t).
      repeat split...
      admit.
      have[G1[G2[[mx[X[rx1[rx2 tyx]]]][pd mrg']]]]:=eval_split H7 wr H1.
      exists (App mx n). exists (B.[n/]).
      repeat split...
      econstructor...
      exact rx1.

    }
    admit.
    inv ev.

  }

