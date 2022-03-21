From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS 
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_validity
  clc_soundness clc_linearity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value : term -> Prop :=
| value_var x : value (Var x)
| value_lam A m s t : value (Lam A m s t)
| value_it : value It
| value_pair m n s : 
  value m ->
  value n ->
  value (Pair m n s)
| value_send m :
  value m ->
  value (Send m).

Inductive eval_context :=
| EHole : eval_context
| EAppL : eval_context -> term -> eval_context
| EAppR m : value m -> eval_context -> eval_context
| EPairL : eval_context -> term -> sort -> eval_context
| EPairR m : value m -> eval_context -> sort -> eval_context
| ELetIn1 : eval_context -> term -> eval_context
| ELetIn2 : eval_context -> term -> eval_context
| ESend : eval_context -> eval_context
| ERecv : eval_context -> eval_context
| EClose : eval_context -> eval_context
| EWait : eval_context -> eval_context.

Declare Scope eval_scope.
Delimit Scope eval_scope with C.
Bind Scope eval_scope with eval_context.
Local Open Scope eval_scope.

Fixpoint plug (e : eval_context) (t : term) : term :=
  match e with
  | EHole => t
  | EAppL e m => App (plug e t) m
  | EAppR m _ e => App m (plug e t)
  | EPairL e m s => Pair (plug e t) m s
  | EPairR m _ e s => Pair m (plug e t) s
  | ELetIn1 e m => LetIn1 (plug e t) m
  | ELetIn2 e m => LetIn2 (plug e t) m
  | ESend e => Send (plug e t)
  | ERecv e => Recv (plug e t)
  | EClose e => Close (plug e t)
  | EWait e => Wait (plug e t)
  end.

Notation "c .[ m ] " := (plug c m)
  (at level 2, m at level 200, left associativity,
    format "c .[ m ]") : eval_scope.

Lemma value_ren v ξ : value v -> value v.[ren ξ]%subst.
Proof with eauto using value.
  move=>val. elim: val ξ=>{v}...
Qed.

Fixpoint eren (e : eval_context) (ξ : var -> var) : eval_context :=
  match e with
  | EHole => EHole
  | EAppL e m => EAppL (eren e ξ) m.[ren ξ]
  | EAppR m v e => EAppR (value_ren ξ v) (eren e ξ)
  | EPairL e m s => EPairL (eren e ξ) m.[ren ξ] s
  | EPairR m v e s => EPairR (value_ren ξ v) (eren e ξ) s
  | ELetIn1 e m => ELetIn1 (eren e ξ) m.[ren ξ]
  | ELetIn2 e m => ELetIn2 (eren e ξ) m.[upn 2 (ren ξ)]
  | ESend e => ESend (eren e ξ)
  | ERecv e => ERecv (eren e ξ)
  | EClose e => EClose (eren e ξ)
  | EWait e => EWait (eren e ξ)
  end%subst.

Lemma plug_inv Γ c m A s : 
  ok Γ -> Γ ⊢ c.[m] : A : s -> 
  exists Γ1 Γ2 B t,
    Γ1 ∘ Γ2 => Γ /\
    Γ1 ⊢ m : B : t /\
    (~Γ1 |> U ->
    forall Γ3 Γ' n,
      Γ3 ∘ Γ2 => Γ' ->
      Γ3 ⊢ n : B : t ->
      Γ' ⊢ c.[n] : A : s).
Proof with eauto using clc_type, merge_reR, merge_pure.
  move e:(c.[m])=>n wf ty. 
  elim: ty wf c m e=>{Γ n A s}.
  move=>Γ s l k wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ.  exists (U @ l.+1). exists U.
    repeat split...
    move=>//. }
  move=>Γ A B s r t i k tyA _ tyB _ wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (t @ i). exists U.
    repeat split...
    move=>//. }
  move=>Γ x A s hs wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists [Γ]. exists A. exists s.
    repeat split...
    move=>k Γ3 Γ' n mrg tyn//=.
    have->//:=merge_pureR mrg (re_pure _). }
  move=>Γ A B m s r t i k tyP _ tym _ wf c m0 e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists [Γ]. exists (Pi A B s r t). exists t.
    repeat split...
    move=>k' Γ3 Γ' n mrg tyn//=.
    have->//:=merge_pureR mrg (re_pure _). }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn wf c m0 e.
  { destruct c; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists B.[n/]. exists r.
      repeat split...
      move=>k' Γ3 Γ' n0 mrg' tyn0//=.
      have->//:=merge_pureR mrg' (re_pure _). }
    { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
      have{ihm ihn}[G1[G2[B0[t0[mrg0[tym0 ih]]]]]]:=ihm wf1 _ _ erefl.
      have[G3[mrg1 mrg2]]:=merge_splitL mrg (merge_sym mrg0).
      exists G1. exists G3. exists B0. exists t0.
      repeat split...
      apply: merge_sym...
      move=>k' Γ3 Γ' n0 mrg3 tyn0//=.
      have[G4[mrg4 mrg5]]:=merge_splitL (merge_sym mrg3) mrg1.
      have{}ih:=ih k' _ _ _ (merge_sym mrg4) tyn0.
      econstructor... }
    { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
      have{ihm ihn}[G1[G2[B0[t0[mrg0[tym0 ih]]]]]]:=ihn wf2 _ _ erefl.
      have[G3[mrg1 mrg2]]:=merge_splitL (merge_sym mrg) (merge_sym mrg0).
      exists G1. exists G3. exists B0. exists t0.
      repeat split...
      apply: merge_sym...
      move=>k' Γ3 Γ' n0 mrg3 tyn0//=.
      have[G4[mrg4 mrg5]]:=merge_splitL (merge_sym mrg3) mrg1.
      have{}ih:=ih k' _ _ _ (merge_sym mrg4) tyn0.
      destruct s.
      have[]//:=merge_pure_inv mrg0 k.
      have[lP tyP]:=validity wf1 tym.
      have[l[tyA[_ tyB]]]:=pi_inv tyP.
      have os:of_sort (_: [Γ1]) 0 None by constructor.
      have oc:=narity tyB os.
      have->:=nsubst_subst c.[m0] c.[n0] oc.
      econstructor.
      apply: (key_impure G4).
      apply: (merge_sym mrg5).
      all: eauto. } }
  move=>Γ k wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (U @ 0). exists U.
    repeat split...
    move=>//. }
  move=>Γ k wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists Unit. exists U.
    repeat split...
    move=>//. }
  move=>Γ A B s r t i lte k tyA _ tyB _ wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (t @ i). exists U.
    repeat split...
    move=>//. }
  move=>Γ1 Γ2 Γ A B m n s r t i k1 k2 mrg 
    tyS ihS tym ihm tyn ihn wf c m0 e.
  { destruct c; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists (Sigma A B s r t). exists t.
      repeat split...
      move=>k' Γ3 Γ' n0 mrg' tyn0//=.
      have->//:=merge_pureR mrg' (re_pure _). }
    { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
      have{ihm ihn}[G1[G2[B0[t0[mrg0[tym0 ih]]]]]]:=ihm wf1 _ _ erefl.
      have[G3[mrg1 mrg2]]:=merge_splitL mrg (merge_sym mrg0).
      exists G1. exists G3. exists B0. exists t0.
      repeat split...
      apply: merge_sym...
      move=>k' Γ3 Γ' n0 mrg3 tyn0//=.
      have[G4[mrg4 mrg5]]:=merge_splitL (merge_sym mrg3) mrg1.
      have{}ih:=ih k' _ _ _ (merge_sym mrg4) tyn0.
      destruct s.
      have[]//:=merge_pure_inv mrg0 k1.
      have//=[G5[G6[l[_[mrg6[tyA tyB]]]]]]:=sigma_inv tyS.
      have[_[e1 e2]]:=merge_re_re mrg5.
      have[_[e3 e4]]:=merge_re_re mrg.
      econstructor.
      apply: (key_impure G4).
      apply: k2.
      all: eauto.
      rewrite<-e2. rewrite e4...
      have os:of_sort (_: [G6]) 0 None by constructor.
      have oc:=narity tyB os.
      have->//:=nsubst_subst c.[n0] c.[m0] oc. }
    { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
      have{ihm ihn}[G1[G2[B0[t0[mrg0[tym0 ih]]]]]]:=ihn wf2 _ _ erefl.
      have[G3[mrg1 mrg2]]:=merge_splitL (merge_sym mrg) (merge_sym mrg0).
      exists G1. exists G3. exists B0. exists t0.
      repeat split...
      apply: merge_sym...
      move=>k' Γ3 Γ' n0 mrg3 tyn0//=.
      have[G4[mrg4 mrg5]]:=merge_splitL (merge_sym mrg3) mrg1.
      have{}ih:=ih k' _ _ _ (merge_sym mrg4) tyn0.
      destruct r.
      have[]//:=merge_pure_inv mrg0 k2.
      have[_[e1 e2]]:=merge_re_re mrg5.
      have[_[e3 e4]]:=merge_re_re mrg.
      econstructor.
      apply: k1.
      apply: (key_impure G4).
      apply: merge_sym...
      rewrite<-e2. rewrite e3...
      all: eauto. } }
  move=>Γ1 Γ2 Γ m n A s mrg tym ihm tyn _ wf c m0 e.
  { destruct c; simpl in e; inv e. 
    { exists Γ. exists [Γ]. exists A. exists s.
      repeat split...
      move=>k' Γ3 Γ' m0 mrg0 tym0//=.
      have->//:=merge_pureR mrg0 (re_pure _). }
    { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
      have{ihm}[G1[G2[B0[t0[mrg0[tym0 ih]]]]]]:=ihm wf1 _ _ erefl.
      have[G3[mrg1 mrg2]]:=merge_splitL mrg (merge_sym mrg0).
      exists G1. exists G3. exists B0. exists t0.
      repeat split...
      apply: merge_sym...
      move=>k' Γ3 Γ' n0 mrg3 tyn0//=.
      have[G4[mrg4 mrg5]]:=merge_splitL (merge_sym mrg3) mrg1.
      have{}ih:=ih k' _ _ _ (merge_sym mrg4) tyn0.
      econstructor... } }
  move=>Γ1 Γ2 Γ A B C m n s r t k x i lte key mrg 
    tym ihm tyC _ tyn _ wf c m0 e.
  { destruct c; simpl in e; inv e. 
    { exists Γ. exists [Γ]. exists C.[m/]. exists x.
      repeat split...
      move=>k' Γ3 Γ' m0 mrg0 tym0//=.
      have->//:=merge_pureR mrg0 (re_pure _). }
    { have[wf1 wf2]:=merge_context_ok_inv mrg wf.
      have{ihm}[G1[G2[B0[t0[mrg0[tym0 ih]]]]]]:=ihm wf1 _ _ erefl.
      have[G3[mrg1 mrg2]]:=merge_splitL mrg (merge_sym mrg0).
      exists G1. exists G3. exists B0. exists t0.
      repeat split...
      apply: merge_sym...
      move=>k' Γ3 Γ' n0 mrg3 tyn0//=.
      have[G4[mrg4 mrg5]]:=merge_splitL (merge_sym mrg3) mrg1.
      have{}ih:=ih k' _ _ _ (merge_sym mrg4) tyn0.
      destruct k.
      have[]//:=merge_pure_inv mrg0 key.
      simpl in tyC.
      have os:of_sort (_: [Γ2]) 0 None by constructor.
      have oc:=narity tyC os.
      have->:=nsubst_subst c.[m0] c.[n0] oc.
      econstructor.
      exact: lte.
      apply: (key_impure G4).
      all: eauto. } }
  move=>Γ i k wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (U @ i). exists U.
    repeat split...
    move=>//. }
  move=>Γ i k wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (Proto 0). exists U.
    repeat split...
    move=>//. }
  move=>Γ i k wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (Proto 0). exists U.
    repeat split...
    move=>//. }
  move=>Γ A B s i k tyA _ tyB _ wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (Proto i). exists U.
    repeat split...
    move=>//. }
  move=>Γ A B s i k tyA _ tyB _ wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (Proto i). exists U.
    repeat split...
    move=>//. }
  move=>Γ A i k tyA ihA wf c m e.
  { destruct c; simpl in e; inv e.
    exists Γ. exists Γ. exists (L @ i). exists U.
    repeat split...
    move=>//. }
  move=>Γ A B m s tym ihm wf c m0 e.
  { destruct c; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists (Sigma A (Ch B) s L L). exists L.
      repeat split...
      move=>k' Γ3 Γ' n mrg tyn//=.
      have->//:=merge_pureR mrg (re_pure _). }
    { have{ihm}[G1[G2[B0[t[mrg[tym0 ih]]]]]]:=ihm wf _ _ erefl.
      exists G1. exists G2. exists B0. exists t.
      repeat split... } }
  move=>Γ A B m s tym ihm wf c m0 e.
  { destruct c; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists (Pi A (Ch B) s L L). exists L.
      repeat split...
      move=>k' Γ3 Γ' n mrg tyn//=.
      have->//:=merge_pureR mrg (re_pure _). }
    { have{ihm}[G1[G2[B0[t[mrg[tym0 ih]]]]]]:=ihm wf _ _ erefl.
      exists G1. exists G2. exists B0. exists t.
      repeat split... } }
  move=>Γ m tym ihm wf c m0 e.
  { destruct c; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists Unit. exists U.
      repeat split...
      move=>k' Γ3 Γ' n mrg tyn//=.
      have->//:=merge_pureR mrg (re_pure _). }
    { have{ihm}[G1[G2[B0[t[mrg[tym0 ih]]]]]]:=ihm wf _ _ erefl.
      exists G1. exists G2. exists B0. exists t.
      repeat split... } }
  move=>Γ m tym ihm wf c m0 e.
  { destruct c; simpl in e; inv e.
    { exists Γ. exists [Γ]. exists Unit. exists U.
      repeat split...
      move=>k' Γ3 Γ' n mrg tyn//=.
      have->//:=merge_pureR mrg (re_pure _). }
    { have{ihm}[G1[G2[B0[t[mrg[tym0 ih]]]]]]:=ihm wf _ _ erefl.
      exists G1. exists G2. exists B0. exists t.
      repeat split... } }
  move=>Γ A B m s i sb tym ihm tyB _ wf c m0 e.
  { have{ihm}[G1[G2[B0[t[mrg[tym0 ih]]]]]]:=ihm wf _ _ e.
    exists G1. exists G2. exists B0. exists t.
    repeat split...
    move=>k' Γ3 Γ' n mrg' tyn.
    have{}ih:=ih k' _ _ _ mrg' tyn.
    have[_[e1 e2]]:=merge_re_re mrg.
    have[_[e3 e4]]:=merge_re_re mrg'.
    apply: clc_conv.
    exact: sb.
    exact: ih.
    rewrite<-e4. rewrite e2... }
Qed.

Lemma eren_comp e m ξ :
  (eren e ξ).[m.[ren ξ]%subst]%C = (e.[m]%C).[ren ξ]%subst.
Proof.
  elim: e m ξ=>//=.
  move=>e ih t m ξ. by rewrite ih.
  move=>m v e ih m0 ξ. by rewrite ih.
  move=> e ih t s m ξ. by rewrite ih.
  move=>m v e ih s m0 ξ. by rewrite ih.
  move=>e ih t m ξ. by rewrite ih.
  move=>e ih t m ξ. by rewrite ih.
  move=>e ih m ξ. by rewrite ih.
  move=>e ih m ξ. by rewrite ih.
  move=>e ih m ξ. by rewrite ih.
  move=>e ih m ξ. by rewrite ih.
Qed.
