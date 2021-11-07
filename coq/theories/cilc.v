From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CLC.

Declare Scope clc_scope.
Open Scope clc_scope.

Inductive sort : Type := U | L.

Definition elem T := option (T * sort).

Definition context T := seq (elem T).

Notation "m +u Γ" := (Some (m, U) :: Γ) (at level 30).
Notation "m +l Γ" := (Some (m, L) :: Γ) (at level 30).
Notation "m +{ s } Γ" := (Some (m, s) :: Γ) (at level 30).
Notation "□ Γ" := (None :: Γ) (at level 30).

Reserved Notation "[ Γ₁ ‡ Γ₂ ‡ Γ ]".
Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  [ nil ‡ nil ‡ nil ]
| merge_left Γ₁ Γ₂ Γ m : 
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ m +u Γ₁ ‡ m +u Γ₂ ‡ m +u Γ ] 
| merge_right1 Γ₁ Γ₂ Γ m :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ m +l Γ₁ ‡ □ Γ₂ ‡ m +l Γ ]
| merge_right2 Γ₁ Γ₂ Γ m :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ □ Γ₁ ‡ m +l Γ₂ ‡ m +l Γ ]
| merge_null Γ₁ Γ₂ Γ :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ □ Γ₁ ‡ □ Γ₂ ‡ □ Γ ]
where "[ Γ₁ ‡ Γ₂ ‡ Γ ]" := (merge Γ₁ Γ₂ Γ).

Reserved Notation "[ Γ ]".

Inductive pure T : context T -> Prop :=
| pure_nil :
  [ nil ]
| pure_u Γ m : 
  [ Γ ] ->
  [ m +u Γ ]
| pure_n Γ : 
  [ Γ ] ->
  [ □ Γ ]
where "[ Γ ]" := (pure Γ).

Reserved Notation "[ x :u A ∈ Γ ]".
Inductive hasU {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| hasU_O m Γ :
  [ Γ ] ->
  [ 0 :u m.[ren (+1)] ∈ m +u Γ ]
| hasU_S Γ v m n : 
  [ v :u m ∈ Γ ] ->
  [ v.+1 :u m.[ren (+1)] ∈ n +u Γ ]
| hasU_N Γ v m : 
  [ v :u m ∈ Γ ] ->
  [ v.+1 :u m.[ren (+1)] ∈ □ Γ ]
where "[ x :u A ∈ Γ ]" := (hasU Γ x A).

Reserved Notation "[ x :l A ∈ Γ ]".
Inductive hasL {T} `{Ids T} `{Subst T} :
  context T -> var -> T -> Prop :=
| hasL_O m Γ :
  [ Γ ] ->
  [ 0 :l m.[ren (+1)] ∈ m +l Γ ]
| hasL_S Γ v m n :
  [ v :l m ∈ Γ ] ->
  [ v.+1 :l m.[ren (+1)] ∈ n +u Γ ]
| hasL_N Γ v m :
  [ v :l m ∈ Γ ] ->
  [ v.+1 :l m.[ren (+1)] ∈ □ Γ ]
where "[ x :l A ∈ Γ ]" := (hasL Γ x A).

Fixpoint re T (Γ : context T) : context T :=
  match Γ with
  | Some (m, U) :: Γ => Some (m, U) :: re Γ
  | _ :: Γ => None :: re Γ
  | _ => nil
  end.

Notation "% Γ" := (re Γ) (at level 30).

Lemma merge_sym T (Γ₁ Γ₂ Γ : context T) : 
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ₂ ‡ Γ₁ ‡ Γ ].
Proof.
  induction 1; intros; constructor; eauto.
Qed.

Lemma merge_pure T (Γ : context T) :
  [ Γ ] -> [ Γ ‡ Γ ‡ Γ ].
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma merge_re1 T (Γ : context T) :
  [ %Γ ‡ Γ ‡ Γ ].
Proof.
  induction Γ.
  - simpl; constructor.
  - destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto.
Qed.

Lemma merge_re2 T (Γ : context T) :
  [ Γ ‡ %Γ ‡ Γ ].
Proof.
  induction Γ.
  - simpl; constructor.
  - destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto.
Qed.

Lemma merge_pure_inv T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ ] -> [ Γ₁ ] /\ [ Γ₂ ].
Proof.
  induction 1; intros; constructor; eauto.
  - inv H0.
    constructor; firstorder.
  - inv H0.
    constructor; firstorder.
  - inv H0.
  - inv H0.
  - inv H0.
  - inv H0.
  - inv H0.
    constructor; firstorder.
  - inv H0.
    constructor; firstorder.
Qed.

Lemma merge_pure1 T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ₁ ] -> Γ = Γ₂.
Proof.
  induction 1; intros; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_pure2 T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ₂ ] -> Γ = Γ₁.
Proof.
  induction 1; intros; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H0.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_pure_pure T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ₁ ] -> [ Γ₂ ] -> [ Γ ].
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    constructor; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    constructor; eauto.
Qed.

Lemma merge_pure_eq T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ₁ ] -> [ Γ₂ ] -> Γ₁ = Γ₂.
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_re_re T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> %Γ₁ = %Γ /\ %Γ₂ = %Γ.
Proof.
  induction 1; simpl; intros; eauto; firstorder.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H0; eauto.
  rewrite H1; eauto.
Qed.

Lemma merge_re_re_re T (Γ : context T) : 
  [ %Γ ‡ %Γ ‡ %Γ ].
Proof.
  induction Γ; intros.
  constructor.
  destruct a.
  destruct p.
  destruct s.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

Lemma re_re T (Γ : context T) :
  %Γ = %(%Γ).
Proof.
  induction Γ.
  - simpl.
    reflexivity.
  - case a; intros; simpl.
    case p; intros; simpl.
    case s; intros; simpl.
    rewrite <- IHΓ; eauto.
    rewrite <- IHΓ; eauto.
    rewrite <- IHΓ; eauto.
Qed.

Lemma pure_re T (Γ : context T) :
  [ Γ ] -> Γ = %Γ.
Proof.
  induction Γ; intros.
  - eauto.
  - inv H; simpl.
    rewrite <- IHΓ; eauto.
    rewrite <- IHΓ; eauto.
Qed.

Lemma re_pure T (Γ : context T) : [ %Γ ].
Proof.
  induction Γ; intros.
  constructor.
  destruct a; simpl. 
  destruct p; simpl. 
  destruct s; simpl. 
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :u A ∈ Γ ] -> [ x :u A ∈ %Γ ].
Proof.
  induction 1; simpl.
  - constructor.
    rewrite <- pure_re; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Γ : context T) :
  forall x A, ~[ x :l A ∈ %Γ ].
Proof.
  induction Γ; unfold not; intros.
  - simpl in H1. inv H1.
  - destruct a; inv H1. 
    destruct p; inv H2. 
    destruct s; inv H4. 
    destruct p; inv H2. 
    destruct s; inv H4. 
    eapply IHΓ; eauto.
    destruct p; inv H2. 
    destruct s; inv H4. 
    eapply IHΓ; eauto.
    eapply IHΓ; eauto.
Qed.

Lemma hasU_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :u A ∈ Γ ] -> [ Γ ].
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma hasL_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :l A ∈ Γ ] -> ~[ Γ ].
Proof.
  induction 1; simpl; intro h. 
  inv h.
  inv h; eauto.
  inv h; eauto.
Qed.

Lemma hasU_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :u A ∈ Γ ] ->
  forall B,
    [ x :u B ∈ Γ ] ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasU in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasU in H5. rewrite H5; eauto.
Qed.

Lemma hasL_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :l A ∈ Γ ] ->
  forall B,
    [ x :l B ∈ Γ ] ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasL in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasL in H5. rewrite H5; eauto.
Qed.

Lemma hasU_hasL {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :u A ∈ Γ ] ->
  forall B,
    ~ [ x :l B ∈ Γ ].
Proof.
  induction 1; unfold not; intros.
  inv H2.
  inv H2; apply IHhasU in H7; eauto.
  inv H2; apply IHhasU in H5; eauto.
Qed.

Lemma merge_split1 T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ] ->
  forall Δ₁ Δ₂,
    [ Δ₁ ‡ Δ₂ ‡ Γ₁ ] ->
    exists Δ,
      [ Δ₁ ‡ Γ₂ ‡ Δ ] /\ [ Δ ‡ Δ₂ ‡ Γ ].
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +u x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m +l x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (□ x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +l x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (□ x).
    repeat constructor; eauto.
Qed.

Lemma merge_split2 T (Γ₁ Γ₂ Γ : context T) :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  forall Δ₁ Δ₂,
    [ Δ₁ ‡ Δ₂ ‡ Γ₁ ] ->
    exists Δ,
      [ Δ₂ ‡ Γ₂ ‡ Δ ] /\ [ Δ₁ ‡ Δ ‡ Γ ].
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +u x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (□ x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m +l x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +l x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (□ x).
    repeat constructor; eauto.
Qed.

Inductive term : Type :=
| Var    (x : var)
| Sort   (s : sort) (l : option nat)
| Prod   (A : term) (B : {bind term}) (s : sort)
| Lolli  (A : term) (B : {bind term}) (s : sort)
| Lam    (n : {bind term})
| App    (m n : term)
| Ind    (A : term) (s : sort) (Cs : list {bind term})
| Constr (i : nat) (m : term)
| Case   (m Q : term) (Fs : list term)
| DCase  (m Q : term) (Fs : list term)
| Fix    (m : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Definition spine (h : term) (ms : list term) : term :=
  List.fold_left (fun acc m => App acc m) ms h.

Inductive iget : nat -> list term -> term -> Prop :=
| iget_O m ls :
  iget 0 (m :: ls) m
| iget_S n m m' ls :
  iget n ls m ->
  iget (S n) (m' :: ls) m.

Inductive step : term -> term -> Prop :=
| step_Lam m m' :
  step m m' ->
  step (Lam m) (Lam m')
| step_AppL m m' n :
  step m m' ->
  step (App m n) (App m' n)
| step_AppR m n n' :
  step n n' ->
  step (App m n) (App m n')
| step_beta m n :
  step (App (Lam m) n) m.[n/]
| step_ProdL A A' B s :
  step A A' ->
  step (Prod A B s) (Prod A' B s)
| step_ProdR A B B' s :
  step B B' ->
  step (Prod A B s) (Prod A B' s)
| step_LolliL A A' B s :
  step A A' ->
  step (Lolli A B s) (Lolli A' B s)
| step_LolliR A B B' s :
  step B B' ->
  step (Lolli A B s) (Lolli A B' s)
| step_IndA A A' s Cs :
  step A A' ->
  step (Ind A s Cs) (Ind A' s Cs)
| step_IndCs A s Cs Cs' :
  step' Cs Cs' ->
  step (Ind A s Cs) (Ind A s Cs')
| step_Constr i m m' :
  step m m' ->
  step (Constr i m) (Constr i m')
| step_CaseM m m' Q Fs :
  step m m' ->
  step (Case m Q Fs) (Case m' Q Fs)
| step_CaseQ m Q Q' Fs :
  step Q Q' ->
  step (Case m Q Fs) (Case m Q' Fs)
| step_CaseFs m Q Fs Fs' :
  step' Fs Fs' ->
  step (Case m Q Fs) (Case m Q Fs') 
| step_CaseIota i m ms Q Fs F :
  iget i Fs F ->
  step 
    (Case (spine (Constr i m) ms) Q Fs)
    (spine F ms)
| step_DCaseM m m' Q Fs :
  step m m' ->
  step (DCase m Q Fs) (DCase m' Q Fs)
| step_DCaseQ m Q Q' Fs :
  step Q Q' ->
  step (DCase m Q Fs) (DCase m Q' Fs)
| step_DCaseFs m Q Fs Fs' :
  step' Fs Fs' ->
  step (DCase m Q Fs) (DCase m Q Fs')
| step_DCaseIota i m ms Q Fs F :
  iget i Fs F ->
  step 
    (DCase (spine (Constr i m) ms) Q Fs)
    (spine F ms)
| step_Fix m m' :
  step m m' ->
  step (Fix m) (Fix m')
| step_FixIota m :
  step (Fix m) (m.[Fix m/])

with step' : list term -> list term -> Prop :=
| step'_nil : step' nil nil
| step'_cons1 m m' ls :
  step m m' ->
  step' (m :: ls) (m' :: ls)
| step'_cons2 m ls ls' :
  step' ls ls' ->
  step' (m :: ls) (m :: ls').

Inductive pstep : term -> term -> Prop :=
| pstep_Var x :
  pstep (Var x) (Var x)
| pstep_Sort srt l :
  pstep (Sort srt l) (Sort srt l)
| pstep_Lam n n' : 
  pstep n n' -> 
  pstep (Lam n) (Lam n')
| pstep_App m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam m) n) (m'.[n'/])
| pstep_Prod A A' s B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Prod A B s) 
        (Prod A' B' s)
| pstep_Lolli A A' s B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Lolli A B s) 
        (Lolli A' B' s)
| pstep_Ind A A' s Cs Cs' :
  pstep A A' ->
  pstep' Cs Cs' ->
  pstep (Ind A s Cs) (Ind A' s Cs')
| pstep_Constr i m m' :
  pstep m m' ->
  pstep (Constr i m) (Constr i m')
| pstep_Case m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  pstep' Fs Fs' ->
  pstep (Case m Q Fs) (Case m' Q' Fs')
| pstep_CaseIota i m ms ms' Q Fs Fs' F F' :
  iget i Fs' F' ->
  pstep' ms ms' ->
  pstep' Fs Fs' ->
  pstep F F' ->
  pstep 
    (Case (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_DCase m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  pstep' Fs Fs' ->
  pstep (DCase m Q Fs) (DCase m' Q' Fs')
| pstep_DCaseIota i m ms ms' Q Fs Fs' F F' :
  iget i Fs' F' ->
  pstep' ms ms' ->
  pstep' Fs Fs' ->
  pstep F F' ->
  pstep 
    (DCase (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_Fix m m' :
  pstep m m' ->
  pstep (Fix m) (m'.[Fix m'/])

with pstep' : list term -> list term -> Prop :=
| pstep'_nil : pstep' nil nil
| pstep'_cons m m' ls ls' :
  pstep m m' ->
  pstep' ls ls' ->
  pstep' (m :: ls) (m' :: ls').