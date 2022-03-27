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
Notation "+n Γ" := (None :: Γ) (at level 30).

Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  merge nil nil nil
| merge_left Γ1 Γ2 Γ m : 
  merge Γ1 Γ2 Γ ->
  merge (m +u Γ1) (m +u Γ2) (m +u Γ)
| merge_right1 Γ1 Γ2 Γ m :
  merge Γ1 Γ2 Γ ->
  merge (m +l Γ1) (+n Γ2) (m +l Γ)
| merge_right2 Γ1 Γ2 Γ m :
  merge Γ1 Γ2 Γ ->
  merge (+n Γ1) (m +l Γ2) (m +l Γ)
| merge_null Γ1 Γ2 Γ :
  merge Γ1 Γ2 Γ ->
  merge (+n Γ1) (+n Γ2) (+n Γ).

Inductive pure T : context T -> Prop :=
| pure_nil :
  pure nil
| pure_u Γ m : 
  pure Γ ->
  pure (m +u Γ)
| pure_n Γ : 
  pure Γ ->
  pure (+n Γ).

Inductive hasU {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| hasU_O m Γ :
  pure Γ ->
  hasU (m +u Γ) 0 m.[ren (+1)]
| hasU_S Γ v m n : 
  hasU Γ v m ->
  hasU (n +u Γ) v.+1 m.[ren (+1)]
| hasU_N Γ v m : 
  hasU Γ v m ->
  hasU (+n Γ) v.+1 m.[ren (+1)].

Inductive hasL {T} `{Ids T} `{Subst T} :
  context T -> var -> T -> Prop :=
| hasL_O m Γ :
  pure Γ ->
  hasL (m +l Γ) 0 m.[ren (+1)]
| hasL_S Γ v m n :
  hasL Γ v m ->
  hasL (n +u Γ) v.+1 m.[ren (+1)]
| hasL_N Γ v m :
  hasL Γ v m ->
  hasL (+n Γ) v.+1 m.[ren (+1)].

Fixpoint re T (Γ : context T) : context T :=
  match Γ with
  | Some (m, U) :: Γ => Some (m, U) :: re Γ
  | _ :: Γ => None :: re Γ
  | _ => nil
  end.

Lemma merge_sym T (Γ1 Γ2 Γ : context T) : 
  merge Γ1 Γ2 Γ -> merge Γ2 Γ1 Γ.
Proof.
  induction 1; intros; constructor; eauto.
Qed.

Lemma merge_pure T (Γ : context T) :
  pure Γ -> merge Γ Γ Γ.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma merge_re1 T (Γ : context T) :
  merge (re Γ) Γ Γ.
Proof.
  induction Γ.
  { simpl; constructor. }
  { destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto. }
Qed.

Lemma merge_re2 T (Γ : context T) :
  merge Γ (re Γ) Γ.
Proof.
  induction Γ.
  { simpl; constructor. }
  { destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto. }
Qed.

Lemma merge_pure_inv T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ -> 
  pure Γ -> 
  pure Γ1 /\ pure Γ2.
Proof.
  induction 1; intros; constructor; eauto; 
  try solve[inv H0; constructor; firstorder].
Qed.

Lemma merge_pure1 T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ -> 
  pure Γ1 -> 
  Γ = Γ2.
Proof.
  induction 1; intros; eauto; try solve[inv H0].
  { inv H0.
    rewrite IHmerge; eauto. }
  { inv H0.
    rewrite IHmerge; eauto. }
  { inv H0.
    rewrite IHmerge; eauto. }
Qed.

Lemma merge_pure2 T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ -> 
  pure Γ2 -> 
  Γ = Γ1.
Proof.
  induction 1; intros; eauto; try solve[inv H0].
  { inv H0.
    rewrite IHmerge; eauto. } 
  { inv H0.
    rewrite IHmerge; eauto. }
  { inv H0.
    rewrite IHmerge; eauto. }
Qed.

Lemma merge_pure_pure T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ -> 
  pure Γ1 ->
  pure Γ2 ->
  pure Γ.
Proof.
  induction 1; intros; eauto.
  { inv H0; inv H1.
    constructor; eauto. }
  { inv H0. }
  { inv H1. }
  { inv H0; inv H1.
    constructor; eauto. }
Qed.

Lemma merge_pure_eq T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ -> 
  pure Γ1 -> 
  pure Γ2 -> 
  Γ1 = Γ2.
Proof.
  induction 1; intros; eauto.
  { inv H0; inv H1.
    rewrite IHmerge; eauto. }
  { inv H0. }
  { inv H1. }
  { inv H0; inv H1.
    rewrite IHmerge; eauto. }
Qed.

Lemma merge_re_re T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ -> 
  re Γ1 = re Γ /\ re Γ2 = re Γ.
Proof.
  induction 1; simpl; intros; eauto; firstorder.
  { rewrite H0; eauto. }
  { rewrite H1; eauto. }
  { rewrite H0; eauto. }
  { rewrite H1; eauto. }
  { rewrite H0; eauto. }
  { rewrite H1; eauto. }
  { rewrite H0; eauto. }
  { rewrite H1; eauto. }
Qed.

Lemma merge_re_re_re T (Γ : context T) : 
  merge (re Γ) (re Γ) (re Γ).
Proof.
  induction Γ; intros.
  { constructor. }
  { destruct a.
    { destruct p.
      destruct s.
      { constructor; eauto. }
      { constructor; eauto. } }
    { constructor; eauto. } }
Qed.

Lemma re_re T (Γ : context T) :
  re Γ = re (re Γ).
Proof.
  induction Γ.
  { simpl.
    reflexivity. }
  { case a; intros; simpl.
    { case p; intros; simpl.
      case s; intros; simpl.
      { rewrite <- IHΓ; eauto. }
      { rewrite <- IHΓ; eauto. } }
    { rewrite <- IHΓ; eauto. } }
Qed.

Lemma pure_re T (Γ : context T) :
  pure Γ -> Γ = re Γ.
Proof.
  induction Γ; intros.
  { eauto. }
  { inv H; simpl.
    { rewrite <- IHΓ; eauto. }
    { rewrite <- IHΓ; eauto. } }
Qed.

Lemma re_pure T (Γ : context T) : pure (re Γ).
Proof.
  induction Γ; intros.
  { constructor. }
  { destruct a; simpl. 
    { destruct p; simpl. 
      destruct s; simpl. 
      { constructor; eauto. }
      { constructor; eauto. } }
    { constructor; eauto. } }
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  hasU Γ x A -> hasU (re Γ) x A.
Proof.
  induction 1; simpl.
  { constructor.
    rewrite <- pure_re; eauto. }
  { constructor; eauto. }
  { constructor; eauto. }
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Γ : context T) :
  forall x A, ~hasL (re Γ) x A.
Proof.
  induction Γ; unfold not; intros.
  { simpl in H1. inv H1. }
  { destruct a; inv H1. 
    { destruct p; inv H2. 
      destruct s; inv H4. } 
    { destruct p; inv H2. 
      destruct s; inv H4. 
      eapply IHΓ; eauto. }
    { destruct p; inv H2. 
      destruct s; inv H4. 
      eapply IHΓ; eauto. }
    { eapply IHΓ; eauto. } }
Qed.

Lemma hasU_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  hasU Γ x A -> pure Γ.
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma hasL_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  hasL Γ x A -> ~pure Γ.
Proof.
  induction 1; simpl; intro h. 
  { inv h. }
  { inv h; eauto. }
  { inv h; eauto. }
Qed.

Lemma hasU_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  hasU Γ x A -> forall B, hasU Γ x B -> A = B.
Proof.
  induction 1; intros.
  { inv H2; eauto. }
  { inv H2; eauto.
    apply IHhasU in H7. rewrite H7; eauto. }
  { inv H2; eauto.
    apply IHhasU in H5. rewrite H5; eauto. }
Qed.

Lemma hasL_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  hasL Γ x A -> forall B, hasL Γ x B -> A = B.
Proof.
  induction 1; intros.
  { inv H2; eauto. }
  { inv H2; eauto.
    apply IHhasL in H7. rewrite H7; eauto. }
  { inv H2; eauto.
    apply IHhasL in H5. rewrite H5; eauto. }
Qed.

Lemma hasU_hasL {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  hasU Γ x A -> forall B, ~hasL Γ x B.
Proof.
  induction 1; unfold not; intros.
  { inv H2. }
  { inv H2; apply IHhasU in H7; eauto. }
  { inv H2; apply IHhasU in H5; eauto. }
Qed.

Lemma merge_split1 T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ ->
  forall Δ1 Δ2,
    merge Δ1 Δ2 Γ1 ->
    exists Δ,
      merge Δ1 Γ2 Δ /\ merge Δ Δ2 Γ.
Proof.
  induction 1; intros.
  { inv H.
    exists nil.
    repeat constructor; eauto. }
  { inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +u x).
    repeat constructor; eauto. }
  { inv H0.
    { specialize (IHmerge _ _ H4).
      firstorder.
      exists (m +l x).
      repeat constructor; eauto. }
    { specialize (IHmerge _ _ H4).
      firstorder.
      exists (+n x).
      repeat constructor; eauto. } }
  { inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +l x).
    repeat constructor; eauto. }
  { inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (+n x).
    repeat constructor; eauto. }
Qed.

Lemma merge_split2 T (Γ1 Γ2 Γ : context T) :
  merge Γ1 Γ2 Γ ->
  forall Δ1 Δ2,
    merge Δ1 Δ2 Γ1 ->
    exists Δ,
      merge Δ2 Γ2 Δ /\ merge Δ1 Δ Γ.
Proof.
  induction 1; intros.
  { inv H.
    exists nil.
    repeat constructor; eauto. }
  { inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +u x).
    repeat constructor; eauto. }
  { inv H0.
    { specialize (IHmerge _ _ H4).
      firstorder.
      exists (+n x).
      repeat constructor; eauto. }
    { specialize (IHmerge _ _ H4).
      firstorder.
      exists (m +l x).
      repeat constructor; eauto. } }
  { inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +l x).
    repeat constructor; eauto. }
  { inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (+n x).
    repeat constructor; eauto. }
Qed.

Lemma merge_merge T (Γ1 Γ2 Γ3 Γ4 Γ : context T) :
  merge Γ1 Γ2 Γ3 ->
  merge Γ3 Γ4 Γ ->
  exists Γ5,
    merge Γ1 Γ4 Γ5 /\
    merge Γ5 Γ2 Γ.
Proof with eauto using merge.
  move=> mg. 
  elim: mg Γ4 Γ=>{Γ1 Γ2 Γ3}; intros.
  { inv H.
    exists nil... }
  { inv H1.
    move: (H0 _ _ H6)=>{H0}[Γ7[mg1 mg2]].
    exists (m +u Γ7)... }
  { inv H1.
    move: (H0 _ _ H6)=>{H0}[Γ7[mg1 mg2]].
    exists (m +l Γ7)... }
  { inv H1.
    move: (H0 _ _ H6)=>{H0}[Γ7[mg1 mg2]].
    exists (+n Γ7)... }
  { inv H1.
    { move: (H0 _ _ H3)=>{H3}[Γ7[mg1 mg2]].
      exists (m +l Γ7)... }
    { move: (H0 _ _ H3)=>{H3}[Γ7[mg1 mg2]].
      exists (+n Γ7)... } }
Qed.