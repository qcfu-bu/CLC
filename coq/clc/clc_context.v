From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sort : Type := U | L.

Definition elem T := option (T * sort).

Definition context T := seq (elem T).

Notation "m +u Γ" := (Some (m, U) :: Γ) (at level 30).
Notation "m +l Γ" := (Some (m, L) :: Γ) (at level 30).
Notation "m +{ s } Γ" := (Some (m, s) :: Γ) (at level 30).
Notation "□ Γ" := (None :: Γ) (at level 30).

Reserved Notation "[ Γ1 ‡ Γ2 ‡ Γ ]".
Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  [ nil ‡ nil ‡ nil ]
| merge_left Γ1 Γ2 Γ m : 
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ m +u Γ1 ‡ m +u Γ2 ‡ m +u Γ ] 
| merge_right1 Γ1 Γ2 Γ m :
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ m +l Γ1 ‡ □ Γ2 ‡ m +l Γ ]
| merge_right2 Γ1 Γ2 Γ m :
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ □ Γ1 ‡ m +l Γ2 ‡ m +l Γ ]
| merge_null Γ1 Γ2 Γ :
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  [ □ Γ1 ‡ □ Γ2 ‡ □ Γ ]
where "[ Γ1 ‡ Γ2 ‡ Γ ]" := (merge Γ1 Γ2 Γ).

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

Lemma merge_sym T (Γ1 Γ2 Γ : context T) : 
  [ Γ1 ‡ Γ2 ‡ Γ ] -> [ Γ2 ‡ Γ1 ‡ Γ ].
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

Lemma merge_pure_inv T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] -> [ Γ ] -> [ Γ1 ] /\ [ Γ2 ].
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

Lemma merge_pure1 T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] -> [ Γ1 ] -> Γ = Γ2.
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

Lemma merge_pure2 T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] -> [ Γ2 ] -> Γ = Γ1.
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

Lemma merge_pure_pure T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] -> [ Γ1 ] -> [ Γ2 ] -> [ Γ ].
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    constructor; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    constructor; eauto.
Qed.

Lemma merge_pure_eq T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] -> [ Γ1 ] -> [ Γ2 ] -> Γ1 = Γ2.
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_re_re T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] -> %Γ1 = %Γ /\ %Γ2 = %Γ.
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

Lemma merge_split1 T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ] ->
  forall Δ1 Δ2,
    [ Δ1 ‡ Δ2 ‡ Γ1 ] ->
    exists Δ,
      [ Δ1 ‡ Γ2 ‡ Δ ] /\ [ Δ ‡ Δ2 ‡ Γ ].
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

Lemma merge_split2 T (Γ1 Γ2 Γ : context T) :
  [ Γ1 ‡ Γ2 ‡ Γ ] ->
  forall Δ1 Δ2,
    [ Δ1 ‡ Δ2 ‡ Γ1 ] ->
    exists Δ,
      [ Δ2 ‡ Γ2 ‡ Δ ] /\ [ Δ1 ‡ Δ ‡ Γ ].
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