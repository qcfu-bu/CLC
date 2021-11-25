From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sort : Type := U | L.

Definition elem T := option (T * sort).

Definition context T := seq (elem T).

Notation "m +u Gamma" := (Some (m, U) :: Gamma) (at level 30).
Notation "m +l Gamma" := (Some (m, L) :: Gamma) (at level 30).
Notation "m +{ s } Gamma" := (Some (m, s) :: Gamma) (at level 30).
Notation "+n Gamma" := (None :: Gamma) (at level 30).

Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  merge nil nil nil
| merge_left Gamma1 Gamma2 Gamma m : 
  merge Gamma1 Gamma2 Gamma ->
  merge (m +u Gamma1) (m +u Gamma2) (m +u Gamma)
| merge_right1 Gamma1 Gamma2 Gamma m :
  merge Gamma1 Gamma2 Gamma ->
  merge (m +l Gamma1) (+n Gamma2) (m +l Gamma)
| merge_right2 Gamma1 Gamma2 Gamma m :
  merge Gamma1 Gamma2 Gamma ->
  merge (+n Gamma1) (m +l Gamma2) (m +l Gamma)
| merge_null Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  merge (+n Gamma1) (+n Gamma2) (+n Gamma).

Inductive pure T : context T -> Prop :=
| pure_nil :
  pure nil
| pure_u Gamma m : 
  pure Gamma ->
  pure (m +u Gamma)
| pure_n Gamma : 
  pure Gamma ->
  pure (+n Gamma).

Inductive hasU {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| hasU_O m Gamma :
  pure Gamma ->
  hasU (m +u Gamma) 0 m.[ren (+1)]
| hasU_S Gamma v m n : 
  hasU Gamma v m ->
  hasU (n +u Gamma) v.+1 m.[ren (+1)]
| hasU_N Gamma v m : 
  hasU Gamma v m ->
  hasU (+n Gamma) v.+1 m.[ren (+1)].

Inductive hasL {T} `{Ids T} `{Subst T} :
  context T -> var -> T -> Prop :=
| hasL_O m Gamma :
  pure Gamma ->
  hasL (m +l Gamma) 0 m.[ren (+1)]
| hasL_S Gamma v m n :
  hasL Gamma v m ->
  hasL (n +u Gamma) v.+1 m.[ren (+1)]
| hasL_N Gamma v m :
  hasL Gamma v m ->
  hasL (+n Gamma) v.+1 m.[ren (+1)].

Fixpoint re T (Gamma : context T) : context T :=
  match Gamma with
  | Some (m, U) :: Gamma => Some (m, U) :: re Gamma
  | _ :: Gamma => None :: re Gamma
  | _ => nil
  end.

Lemma merge_sym T (Gamma1 Gamma2 Gamma : context T) : 
  merge Gamma1 Gamma2 Gamma -> merge Gamma2 Gamma1 Gamma.
Proof.
  induction 1; intros; constructor; eauto.
Qed.

Lemma merge_pure T (Gamma : context T) :
  pure Gamma -> merge Gamma Gamma Gamma.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma merge_re1 T (Gamma : context T) :
  merge (re Gamma) Gamma Gamma.
Proof.
  induction Gamma.
  { simpl; constructor. }
  { destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto. }
Qed.

Lemma merge_re2 T (Gamma : context T) :
  merge Gamma (re Gamma) Gamma.
Proof.
  induction Gamma.
  { simpl; constructor. }
  { destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto. }
Qed.

Lemma merge_pure_inv T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma -> 
  pure Gamma1 /\ pure Gamma2.
Proof.
  induction 1; intros; constructor; eauto; 
  try solve[inv H0; constructor; firstorder].
Qed.

Lemma merge_pure1 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma1 -> 
  Gamma = Gamma2.
Proof.
  induction 1; intros; eauto; try solve[inv H0].
  { inv H0.
    rewrite IHmerge; eauto. }
  { inv H0.
    rewrite IHmerge; eauto. }
  { inv H0.
    rewrite IHmerge; eauto. }
Qed.

Lemma merge_pure2 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma2 -> 
  Gamma = Gamma1.
Proof.
  induction 1; intros; eauto; try solve[inv H0].
  { inv H0.
    rewrite IHmerge; eauto. } 
  { inv H0.
    rewrite IHmerge; eauto. }
  { inv H0.
    rewrite IHmerge; eauto. }
Qed.

Lemma merge_pure_pure T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma1 ->
  pure Gamma2 ->
  pure Gamma.
Proof.
  induction 1; intros; eauto.
  { inv H0; inv H1.
    constructor; eauto. }
  { inv H0. }
  { inv H1. }
  { inv H0; inv H1.
    constructor; eauto. }
Qed.

Lemma merge_pure_eq T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma1 -> 
  pure Gamma2 -> 
  Gamma1 = Gamma2.
Proof.
  induction 1; intros; eauto.
  { inv H0; inv H1.
    rewrite IHmerge; eauto. }
  { inv H0. }
  { inv H1. }
  { inv H0; inv H1.
    rewrite IHmerge; eauto. }
Qed.

Lemma merge_re_re T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  re Gamma1 = re Gamma /\ re Gamma2 = re Gamma.
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

Lemma merge_re_re_re T (Gamma : context T) : 
  merge (re Gamma) (re Gamma) (re Gamma).
Proof.
  induction Gamma; intros.
  { constructor. }
  { destruct a.
    { destruct p.
      destruct s.
      { constructor; eauto. }
      { constructor; eauto. } }
    { constructor; eauto. } }
Qed.

Lemma re_re T (Gamma : context T) :
  re Gamma = re (re Gamma).
Proof.
  induction Gamma.
  { simpl.
    reflexivity. }
  { case a; intros; simpl.
    { case p; intros; simpl.
      case s; intros; simpl.
      { rewrite <- IHGamma; eauto. }
      { rewrite <- IHGamma; eauto. } }
    { rewrite <- IHGamma; eauto. } }
Qed.

Lemma pure_re T (Gamma : context T) :
  pure Gamma -> Gamma = re Gamma.
Proof.
  induction Gamma; intros.
  { eauto. }
  { inv H; simpl.
    { rewrite <- IHGamma; eauto. }
    { rewrite <- IHGamma; eauto. } }
Qed.

Lemma re_pure T (Gamma : context T) : pure (re Gamma).
Proof.
  induction Gamma; intros.
  { constructor. }
  { destruct a; simpl. 
    { destruct p; simpl. 
      destruct s; simpl. 
      { constructor; eauto. }
      { constructor; eauto. } }
    { constructor; eauto. } }
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> hasU (re Gamma) x A.
Proof.
  induction 1; simpl.
  { constructor.
    rewrite <- pure_re; eauto. }
  { constructor; eauto. }
  { constructor; eauto. }
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Gamma : context T) :
  forall x A, ~hasL (re Gamma) x A.
Proof.
  induction Gamma; unfold not; intros.
  { simpl in H1. inv H1. }
  { destruct a; inv H1. 
    { destruct p; inv H2. 
      destruct s; inv H4. } 
    { destruct p; inv H2. 
      destruct s; inv H4. 
      eapply IHGamma; eauto. }
    { destruct p; inv H2. 
      destruct s; inv H4. 
      eapply IHGamma; eauto. }
    { eapply IHGamma; eauto. } }
Qed.

Lemma hasU_pure {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> pure Gamma.
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma hasL_pure {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A -> ~pure Gamma.
Proof.
  induction 1; simpl; intro h. 
  { inv h. }
  { inv h; eauto. }
  { inv h; eauto. }
Qed.

Lemma hasU_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> forall B, hasU Gamma x B -> A = B.
Proof.
  induction 1; intros.
  { inv H2; eauto. }
  { inv H2; eauto.
    apply IHhasU in H7. rewrite H7; eauto. }
  { inv H2; eauto.
    apply IHhasU in H5. rewrite H5; eauto. }
Qed.

Lemma hasL_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A -> forall B, hasL Gamma x B -> A = B.
Proof.
  induction 1; intros.
  { inv H2; eauto. }
  { inv H2; eauto.
    apply IHhasL in H7. rewrite H7; eauto. }
  { inv H2; eauto.
    apply IHhasL in H5. rewrite H5; eauto. }
Qed.

Lemma hasU_hasL {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> forall B, ~hasL Gamma x B.
Proof.
  induction 1; unfold not; intros.
  { inv H2. }
  { inv H2; apply IHhasU in H7; eauto. }
  { inv H2; apply IHhasU in H5; eauto. }
Qed.

Lemma merge_split1 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Gamma1 ->
    exists Delta,
      merge Delta1 Gamma2 Delta /\ merge Delta Delta2 Gamma.
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

Lemma merge_split2 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Gamma1 ->
    exists Delta,
      merge Delta2 Gamma2 Delta /\ merge Delta1 Delta Gamma.
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

Lemma merge_merge T (Gamma1 Gamma2 Gamma3 Gamma4 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma3 ->
  merge Gamma3 Gamma4 Gamma ->
  exists Gamma5,
    merge Gamma1 Gamma4 Gamma5 /\
    merge Gamma5 Gamma2 Gamma.
Proof with eauto using merge.
  move=> mg. 
  elim: mg Gamma4 Gamma=>{Gamma1 Gamma2 Gamma3}; intros.
  { inv H.
    exists nil... }
  { inv H1.
    move: (H0 _ _ H6)=>{H0}[Gamma7[mg1 mg2]].
    exists (m +u Gamma7)... }
  { inv H1.
    move: (H0 _ _ H6)=>{H0}[Gamma7[mg1 mg2]].
    exists (m +l Gamma7)... }
  { inv H1.
    move: (H0 _ _ H6)=>{H0}[Gamma7[mg1 mg2]].
    exists (+n Gamma7)... }
  { inv H1.
    { move: (H0 _ _ H3)=>{H3}[Gamma7[mg1 mg2]].
      exists (m +l Gamma7)... }
    { move: (H0 _ _ H3)=>{H3}[Gamma7[mg1 mg2]].
      exists (+n Gamma7)... } }
Qed.