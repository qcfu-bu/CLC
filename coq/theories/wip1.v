From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8.
Require Import AutosubstSsr ARS cc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CLC.

Declare Scope clc_scope.
Open Scope clc_scope.

Inductive sort : Type := Bang | Dot.
Notation "!" := Bang.
Notation "⋅" := Dot.

Definition elem T := option (T * sort).

Definition context T := seq (elem T).

Notation "m ̂+ Γ" := (Some (m, !) :: Γ) (at level 30).
Notation "m ̇+ Γ" := (Some (m, ⋅) :: Γ) (at level 30).
Notation "m +{ s } Γ" := (Some (m, s) :: Γ) (at level 30).
Notation "□ Γ" := (None :: Γ) (at level 30).

Reserved Notation "[ Γ₁ ‡ Γ₂ ‡ Γ ]".
Inductive merge T : context T -> context T -> context T -> Prop :=
| merge_nil :
  [ nil ‡ nil ‡ nil ]
| merge_left Γ₁ Γ₂ Γ m : 
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ m ̂+ Γ₁ ‡ m ̂+ Γ₂ ‡ m ̂+ Γ ] 
| merge_right1 Γ₁ Γ₂ Γ m :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ m ̇+ Γ₁ ‡ □ Γ₂ ‡ m ̇+ Γ ]
| merge_right2 Γ₁ Γ₂ Γ m :
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ □ Γ₁ ‡ m ̇+ Γ₂ ‡ m ̇+ Γ ]
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
  [ m ̂+ Γ ]
| pure_n Γ : 
  [ Γ ] ->
  [ □ Γ ]
where "[ Γ ]" := (pure Γ).

Reserved Notation "[ x :- A ̂∈ Γ ]".
Inductive hasBang {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| hasBang_O m Γ :
  [ Γ ] ->
  [ 0 :- m.[ren (+1)] ̂∈ m ̂+ Γ ]
| hasBang_S Γ v m n : 
  [ v :- m ̂∈ Γ ] ->
  [ v.+1 :- m.[ren (+1)] ̂∈ n ̂+ Γ ]
| hasBang_N Γ v m : 
  [ v :- m ̂∈ Γ ] ->
  [ v.+1 :- m.[ren (+1)] ̂∈ □ Γ ]
where "[ x :- A ̂∈ Γ ]" := (hasBang Γ x A).

Reserved Notation "[ x :- A ̇∈ Γ ]".
Inductive hasDot {T} `{Ids T} `{Subst T} :
  context T -> var -> T -> Prop :=
| hasEpsilon_O m Γ :
  [ Γ ] ->
  [ 0 :- m.[ren (+1)] ̇∈ m ̇+ Γ ]
| hasL_S Γ v m n :
  [ v :- m ̇∈ Γ ] ->
  [ v.+1 :- m.[ren (+1)] ̇∈ n ̂+ Γ ]
| hasL_N Γ v m :
  [ v :- m ̇∈ Γ ] ->
  [ v.+1 :- m.[ren (+1)] ̇∈ □ Γ ]
where "[ x :- A ̇∈ Γ ]" := (hasDot Γ x A).

Fixpoint re T (Γ : context T) : context T :=
  match Γ with
  | Some (m, !) :: Γ => Some (m, !) :: re Γ
  | _ :: Γ => None :: re Γ
  | _ => nil
  end.

Notation "% Γ" := (re Γ) (at level 30).

Lemma merge_sym T (Γ₁ Γ₂ Γ : context T) : 
  [ Γ₁ ‡ Γ₂ ‡ Γ ] -> [ Γ₂ ‡ Γ₁ ‡ Γ ].
Proof.
  induction 1; intros; constructor; eauto.
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

Lemma hasBang_re {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ̂∈ Γ ] -> [ x :- A ̂∈ re Γ ].
Proof.
  induction 1; simpl.
  - constructor.
    rewrite <- pure_re; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma hasDot_re {T} `{Ids T} `{Subst T} (Γ : context T) :
  forall x A, ~[ x :- A ̇∈ %Γ ].
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

Lemma hasBang_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ̂∈ Γ ] -> [ Γ ].
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma hasDot_pure {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ̇∈ Γ ] -> ~[ Γ ].
Proof.
  induction 1; simpl; intro h. 
  inv h.
  inv h; eauto.
  inv h; eauto.
Qed.

Lemma hasBang_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ̂∈ Γ ] ->
  forall B,
    [ x :- B ̂∈ Γ ] ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasBang in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasBang in H5. rewrite H5; eauto.
Qed.

Lemma hasDot_x {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ̇∈ Γ ] ->
  forall B,
    [ x :- B ̇∈ Γ ] ->
    A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasDot in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasDot in H5. rewrite H5; eauto.
Qed.

Lemma hasBang_hasDot {T} `{Ids T} `{Subst T} (Γ : context T) x A :
  [ x :- A ̂∈ Γ ] ->
  forall B,
    ~ [ x :- B ̇∈ Γ ].
Proof.
  induction 1; unfold not; intros.
  inv H2.
  inv H2; apply IHhasBang in H7; eauto.
  inv H2; apply IHhasBang in H5; eauto.
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
    exists (m ̂+ x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m ̇+ x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (□ x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m ̇+ x).
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
    exists (m ̂+ x).
    repeat constructor; eauto.
  - inv H0.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (□ x).
      repeat constructor; eauto.
    + specialize (IHmerge _ _ H4).
      firstorder.
      exists (m ̇+ x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m ̇+ x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (□ x).
    repeat constructor; eauto.
Qed.

Inductive term : Type :=
| Var   (x : var)
| Sort  (s : sort) (l : option nat)
| Lolli (A : term) (B : {bind term}) (s t : sort)
| Lam   (n : {bind term})
| App   (m n : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort srt l    : value (Sort srt l)
| value_var x         : value (Var x)
| value_lolli A B s t : value (Lolli A B s t)
| value_lam n         : value (Lam n).

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta m n :
  (App (Lam m) n) ~> m.[n/]
| step_lam m m' :
  m ~> m' ->
  Lam m ~> Lam m'
| step_lolliL A A' B s t :
  A ~> A' ->
  Lolli A B s t ~> Lolli A' B s t
| step_lolliR A B B' s t :
  B ~> B' ->
  Lolli A B s t ~> Lolli A B' s t
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
where "m ~> n" := (step m n).

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort srt l :
  pstep (Sort srt l) (Sort srt l)
| pstep_lam n n' : 
  pstep n n' -> 
  pstep (Lam n) (Lam n')
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam m) n) (m'.[n'/])
| pstep_lolli A A' s B B' t :
  pstep A A' ->
  pstep B B' ->
  pstep (Lolli A B s t) 
        (Lolli A' B' s t).

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).

Definition sred σ τ :=
  forall x : var, (σ x) ~>* (τ x).

Lemma step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ => /={m n}; eauto using step.
  move=> m n σ. 
  replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
  apply step_beta. autosubst.
Qed.

Lemma red_app m1 m2 n1 n2 :
  m1 ~>* m2 -> n1 ~>* n2 -> (App m1 n1) ~>* (App m2 n2).
Proof.
  move=> A B. apply: (star_trans (App m2 n1)).
  - apply: (star_hom (App^~ n1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_lam s1 s2 : s1 ~>* s2 -> Lam s1 ~>* Lam s2.
Proof. apply: star_hom => x y. exact: step_lam. Qed.

Lemma red_lolli A1 A2 B1 B2 s t :
  A1 ~>* A2 -> B1 ~>* B2 -> Lolli A1 B1 s t ~>* Lolli A2 B2 s t.
Proof.
  move=> A B. apply: (star_trans (Lolli A2 B1 s t)).
  - apply: (star_hom (((Lolli^~ B1)^~ s)^~ t)) A => x y. exact: step_lolliL.
  - apply: (star_hom (((Lolli A2)^~ s)^~ t)) B => x y. exact: step_lolliR.
Qed.

Lemma red_subst m n : 
  m ~>* n -> forall σ, m.[σ] ~>* n.[σ].
Proof.
  induction 1; intros.
  eauto.
  eapply star_trans.
  apply IHstar; eauto.
  econstructor; eauto.
  apply step_subst; eauto.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: red_subst. exact: A. Qed.

Hint Resolve red_app red_lam red_lolli sred_up : red_congr.

Lemma red_compat σ τ s : sred σ τ -> red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with red_congr. Qed.

Definition sconv (σ τ : var -> term) :=
  forall x, σ x === τ x.

Lemma conv_lam s1 s2 : s1 === s2 -> Lam s1 === Lam s2.
Proof. apply: conv_hom => x y. exact: step_lam. Qed.

Lemma conv_lolli A A' s B B' t :
  A === A' -> B === B' -> Lolli A B s t === Lolli A' B' s t.
Proof.
  move=> conv1 conv2. apply: (conv_trans (Lolli A' B s t)).
  - apply: (conv_hom (((Lolli^~ B)^~ s)^~ t)) conv1 => x y ps.
    constructor; eauto.
  - apply: (conv_hom (((Lolli A')^~ s)^~ t)) conv2 => x y ps.
    constructor; eauto.
Qed.

Lemma conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> A B. apply: (conv_trans (App m' n)).
  - apply: (conv_hom (App^~ n)) A => x y ps. 
    constructor; eauto.
  - apply: conv_hom B => x y ps.
    constructor; eauto.
Qed.

Lemma conv_subst σ s t : 
  s === t -> s.[σ] === t.[σ].
Proof. 
  intro H.
  eapply conv_hom; eauto.
  intros.
  apply step_subst; eauto.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Lemma conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof.
  elim: s σ τ => *; asimpl; eauto using
    conv_app, conv_lam, conv_lolli, sconv_up.
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep n n' : step n n' -> pstep n n'.
Proof with eauto using pstep, pstep_refl.
  intros.
  induction H...
Qed.

Lemma pstep_red s t : pstep s t -> s ~>* t.
Proof.
  elim=> {s t} //=; eauto with red_congr.
  move=> m m' n n' p1 r1 p2 r2. eapply starES. by econstructor.
  apply: (star_trans (m'.[n.:Var])). exact: red_subst.
  by apply: red_compat => -[|].
Qed.

Lemma pstep_subst s t : 
  pstep s t -> 
    forall σ, pstep s.[σ] t.[σ].
Proof with eauto using pstep, pstep_refl.
  intros.
  dependent induction H...
  - asimpl.
    specialize (IHpstep1 (up σ)).
    specialize (IHpstep2 σ).
    pose proof (pstep_beta IHpstep1 IHpstep2).
    asimpl in H1; eauto.
Qed.

Definition psstep (σ τ : var -> term) := 
  forall x, pstep (σ x) (τ x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl.
  unfold psstep.
  induction x...
Qed.

Lemma psstep_up σ τ :
  psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat s t :
  pstep s t ->
    forall σ τ, 
      psstep σ τ -> pstep s.[σ] t.[τ].
Proof with eauto 6 using pstep, psstep_up.
  intros.
  dependent induction H; asimpl...
  - pose proof (psstep_up H1).
    pose proof (IHpstep1 _ _ H2).
    pose proof (IHpstep2 _ _ H1).
    pose proof (pstep_beta H3 H4).
    asimpl in H5; eauto.
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep, pstep_refl.
  intros.
  apply pstep_compat...
  - apply psstep_compat...
    apply psstep_refl.
Qed.

Lemma pstep_compat_beta m m' :
  pstep m m' -> 
    forall n n',
      pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using psstep_refl, psstep_compat.
  intros.
  apply pstep_compat...
Qed.

Ltac first_order :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : ex2 _ _ |- _ ] => destruct H
  | [ H1 : ?A -> _, H2 : ?A |- _ ] => specialize (H1 H2)
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ |- _ /\ _ ] => split
  end.

Lemma pstep_diamond m m1 :
  pstep m m1 ->
  forall m2, pstep m m2 ->
    exists m', pstep m1 m' /\ pstep m2 m'.
Proof with eauto using pstep.
  intros.
  dependent induction H.
  - inv H0. exists (Var x)...
  - inv H0. exists (Sort srt l)...
  - inv H0. apply (IHpstep) in H2. first_order. exists (Lam x)...
  - inv H1.
    + apply (IHpstep1) in H4. apply (IHpstep2) in H6. first_order.
      exists (App x0 x)...
    + inv H. 
      assert (pstep (Lam m0) (Lam m'0))...
      apply (IHpstep1) in H.  apply (IHpstep2) in H6. first_order.
      inv H.
      inv H3.
      exists (n'2.[x0/]). split.
      apply pstep_beta...
      apply pstep_compat_beta...
  - inv H1.
    + inv H4.
      apply IHpstep1 in H2. apply IHpstep2 in H6. first_order.
      exists (x.[x0/]). split.
      * apply pstep_compat_beta...
      * apply pstep_beta...
    + apply IHpstep1 in H4. apply IHpstep2 in H6. first_order.
      exists (x0.[x/]). split.
      * apply pstep_compat_beta...
      * apply pstep_compat_beta...
  - inv H1. apply (IHpstep1) in H7. apply (IHpstep2) in H8.
    first_order. exists (Lolli x0 x s t)...
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> red m m2 ->
    exists m', red m1 m' /\ pstep m2 m'.
Proof with eauto using pstep_refl, star.
  intros.
  dependent induction H0... first_order.
  pose proof (step_pstep H1).
  pose proof (pstep_diamond H4 H3). first_order.
  exists x0. split...
  eapply star_trans; eauto.
  apply pstep_red; eauto.
Qed.

Theorem confluence :
  confluent step.
Proof with eauto using step, star.
  unfold confluent.
  unfold joinable.
  intros.
  dependent induction H.
  - exists z; eauto.
  - first_order.
    apply step_pstep in H0.
    pose proof (strip H0 H2). first_order.
    exists x1; eauto.
    eapply star_trans.
    apply H3.
    apply pstep_red; eauto.
Qed.
Hint Resolve confluence.

Theorem church_rosser :
  CR step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.
Hint Resolve church_rosser.

Lemma sort_ren_inv s l v xi :
  Sort s l = v.[ren xi] -> v = Sort s l.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma var_ren_inv x v xi :
  Var x = v.[ren xi] -> exists n, v = Var n.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma lolli_ren_inv A B s t v xi :
  Lolli A B s t = v.[ren xi] -> 
  exists A B s t, v = Lolli A B s t.
Proof.
  induction v; asimpl; try discriminate; eauto 6.
Qed.

Lemma lam_ren_inv m v xi :
  Lam m = v.[ren xi] -> exists n, v = Lam n.
Proof.
  induction v; asimpl; try discriminate; eauto.
Qed.

Lemma value_rename xi A :
  value A <-> value A.[ren xi].
Proof.
  split.
  induction 1; asimpl; constructor.
  intros.
  dependent induction H.
  apply sort_ren_inv in x; subst.
  constructor.
  apply var_ren_inv in x.
  inv x.
  constructor.
  apply lolli_ren_inv in x; first_order; subst; constructor.
  apply lam_ren_inv in x; inv x; constructor.
Qed.

Lemma red_sort_inv s l A :
  red (Sort s l) A -> A = (Sort s l).
Proof.
  induction 1; intros; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_lolli_inv A B s t x :
  red (Lolli A B s t) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Lolli A' B' s t.
Proof.
  induction 1.
  - exists A.
    exists B.
    repeat constructor.
  - first_order; subst.
    inv H0.
    + exists A'.
      exists x0.
      first_order; eauto.
      eapply star_trans; eauto.
      econstructor; eauto.
    + exists x.
      exists B'.
      first_order; eauto.
      eapply star_trans; eauto.
      econstructor; eauto.
Qed.

Lemma red_var_inv x y :
  red (Var x) y -> y = Var x.
Proof.
  induction 1; eauto.
  rewrite IHstar in H0.
  inv H0; eauto.
Qed.

Lemma red_lam_inv m n :
  red (Lam m) n ->
  exists m',
    red m m' /\ n = Lam m'.
Proof.
  induction 1.
  - exists m; repeat constructor.
  - first_order; subst.
    inv H0.
    exists m'.
    repeat constructor; eauto using star.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  Sort s1 l1 === Sort s2 l2 ->
  s1 = s2 /\ l1 = l2.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_sort_inv in H0.
  apply red_sort_inv in H1.
  first_order; subst; inv H1; eauto.
Qed.

Lemma lolli_inj A A' B B' s s' t t' :
  Lolli A B s t === Lolli A' B' s' t' ->
  A === A' /\ B === B' /\ s = s' /\ t = t'.
Proof.
  intros.
  apply church_rosser in H.
  inv H.
  apply red_lolli_inv in H0.
  apply red_lolli_inv in H1.
  first_order; subst.
  inv H2; eauto using join_conv.
  inv H2; eauto using join_conv.
  inv H2; eauto.
  inv H2; eauto.
Qed.

Ltac red_inv m H :=
  match m with
  | Var   => apply red_var_inv in H
  | Sort  => apply red_sort_inv in H
  | Lolli => apply red_lolli_inv in H
  | Lam   => apply red_lam_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : red (?m _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
  end;
  first_order; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  | [ H : value (App _ _) |- _ ] => inv H
  end; eauto.

Notation "s @ l" := (Sort s (Some l)) (at level 30).
Notation prop s := (Sort s None).

Inductive sub1 : term -> term -> Prop :=
| sub1_refl A : 
  sub1 A A
| sub1_prop s l : 
  sub1 (prop s) (s @ l)
| sub1_sort s l1 l2 : 
  l1 <= l2 -> 
  sub1 (s @ l1) (s @ l2)
| sub1_lolli A B1 B2 s t : 
  sub1 B1 B2 -> 
  sub1 (Lolli A B1 s t) (Lolli A B2 s t).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : 
  sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 50, no associativity) : clc_scope.

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_prop s n : prop s <: s @ n.
Proof. exact/sub1_sub/sub1_prop. Qed.

Lemma sub_sort s n m : n <= m -> s @ n <: s @ m.
Proof. move=> leq. exact/sub1_sub/sub1_sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto 6 using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D => {A B}
    [ A C D 
    | s l C D conv sb
    | s l1 l2 leq C D conv sb
    | A B1 B2 s t sb1 ih C D conv sb2]...
  - inv sb; try (exfalso; solve_conv)...
    move: conv => /sort_inj [->[eq]].
    apply: sub_prop.
  - inv sb; try (exfalso; solve_conv)...
    move: conv => /sort_inj [->[eq]].
    apply: sub_sort. subst.
    exact: leq_trans leq _.
  - inv sb2; try (exfalso; solve_conv)...
    move: conv => /lolli_inj[conv1 [conv2 [->->]]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    eapply SubI. 
    eapply sub1_lolli... 
    eapply conv_lolli... 
    exact: conv_lolli.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_prop_inv s1 s2 :
  prop s1 <: prop s2 -> s1 = s2.
Proof.
  move=> [s1' s2' []].
  - move=> A c1 c2.
    have{c1 c2}/sort_inj[s l]: prop s1 === prop s2.
     exact: conv_trans c2.
     exact: s.
  - move=> s l /sort_inj[-> _] /sort_inj[-> _] => //.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_sort_inv s1 s2 l1 l2 :
  s1 @ l1 <: s2 @ l2 -> s1 = s2 /\ l1 <= l2.
Proof.
  move=> [s1' s2' []].
  - move=> A c1 c2.
    have{c1 c2}/sort_inj[s l]: s1 @ l1 === s2 @ l2.
     exact: conv_trans c2.
    inv l=> //.
  - move=> s l0 /sort_inj[_ h] => //.
  - move=> s l0 l3 leq /sort_inj[->[->]] /sort_inj[<-[<-]] => //.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_lolli_inv A1 A2 s1 s2 B1 B2 t1 t2 :
  Lolli A1 B1 s1 t1 <: Lolli A2 B2 s2 t2 -> 
  A1 === A2 /\ B1 <: B2 /\ s1 = s2 /\ t1 = t2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/lolli_inj[c1 [c2 [->->]]]: 
      Lolli A1 B1 s1 t1 === Lolli A2 B2 s2 t2.
     exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> *. exfalso; solve_conv.
  - move=> A B0 B3 s t sb /lolli_inj[c1 [c2 [<-<-]]]. 
    move=> /lolli_inj[c3 [c4 [->->]]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst σ A B : sub1 A B -> sub1 A.[σ] B.[σ].
Proof. move=> s. elim: s σ => /=; eauto using sub1. Qed.

Lemma sub_subst σ A B : A <: B -> A.[σ] <: B.[σ].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Lemma sub_ren A B xi : A <: B -> A.[ren xi] <: B.[ren xi].
Proof. move=> *; by apply: sub_subst. Qed.

Reserved Notation "[ Γ |- ]".
Reserved Notation "[ Γ |- m :- A -: s ]".
  
Inductive has_type : context term -> term -> term -> sort -> Prop :=
| p_axiom Γ : 
  [ Γ ] ->
  [ Γ |- prop ! :- ! @ 0 -: ! ]
| s_axiom Γ s l : 
  [ Γ ] ->
  [ Γ |- s @ l :- ! @ l.+1 -: ! ]
| u_prop Γ A B l :
  [ Γ ] ->
  [ Γ |- A :- Sort ! l -: ! ] ->
  [ A ̂+ Γ |- B :- prop ! -: ! ] ->
  [ Γ |- Lolli A B ! ! :- prop ! -: ! ]
| lolli Γ A B r s t l :
  [ Γ ] ->
  [ Γ |- A :- r @ l -: ! ] ->
  [ %(A +{r} Γ) |- B :- s @ l -: ! ] ->
  [ Γ |- Lolli A B r s :- t @ l -: ! ]
| u_var Γ x A : 
  [ x :- A ̂∈ Γ ] ->
  [ Γ |- Var x :- A -: ! ]
| l_var Γ x A :
  [ x :- A ̇∈ Γ ] ->
  [ Γ |- Var x :- A -: ⋅ ]
| u_lam Γ n A s B t l :
  [ Γ ] ->
  [ Γ |- Lolli A B s t :- Sort ! l -: ! ] ->
  [ A +{s} Γ |- n :- B -: t ] ->
  [ Γ |- Lam n :- Lolli A B s t -: ! ]
| l_lam Γ n A s B t l :
  [ %Γ |- Lolli A B s t :- ⋅ @ l -: ! ] ->
  [ A +{s} Γ |- n :- B -: t ] ->
  [ Γ |- Lam n :- Lolli A B s t -: ⋅ ]
| u_app Γ₁ Γ₂ Γ A B s t m n :
  [ Γ₂ ] ->
  [ Γ₁ |- m :- Lolli A B ! s -: t ] ->
  [ Γ₂ |- n :- A -: ! ] ->
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ Γ |- App m n :- B.[n/] -: s ]
| l_app Γ₁ Γ₂ Γ  A B s t m n :
  [ Γ₁ |- m :- Lolli A B ⋅ s -: t ] ->
  [ Γ₂ |- n :- A -: ⋅ ] ->
  [ Γ₁ ‡ Γ₂ ‡ Γ ] ->
  [ Γ |- App m n :- B.[n/] -: s ]
| conversion Γ A B m s l :
  A <: B ->
  [ Γ |- B :- Sort s l -: ! ] ->
  [ Γ |- m :- A -: s ] ->
  [ Γ |- m :- B -: s ]
where "[ Γ |- m :- A -: s ]" := (has_type Γ m A s).

Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| u_ok Γ A l :
  [ Γ |- ] ->
  [ %Γ |- A :- Sort ! l -: ! ] ->
  [ A ̂+ Γ |- ]
| l_ok Γ A l :
  [ Γ |- ] ->
  [ %Γ |- A :- Sort ⋅ l -: ! ] ->
  [ A ̇+ Γ |- ]
| n_ok Γ :
  [ Γ |- ] ->
  [ □ Γ |- ]
where "[ Γ |- ]" := (context_ok Γ).

Lemma re_ok Γ :
  [ Γ |- ] ->
  [ %Γ |- ].
Proof with eauto using context_ok.
  intros.
  induction H...
  simpl.
  eapply u_ok...
  rewrite <- re_re; eauto.
Qed.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_u Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m ̂+ Γ) (m.[ren ξ] ̂+ Γ')
| agree_ren_l Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m ̇+ Γ) (m.[ren ξ] ̇+ Γ')
| agree_ren_n Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (□ Γ) (□ Γ')
| agree_ren_wkU Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) (Γ) (m ̂+ Γ')
| agree_ren_wkN Γ Γ' ξ :
  agree_ren ξ Γ Γ' ->
  agree_ren ((+1) ∘ ξ) (Γ) (□ Γ').

Lemma agree_ren_refl Γ :
  agree_ren id Γ Γ.
Proof.
  induction Γ.
  - constructor.
  - destruct a. 
    destruct p.
    destruct s.
    assert (agree_ren id (t :u Γ) (t :u Γ)
      = agree_ren (upren id) (t :u Γ) (t.[ren id] :u Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (t :l Γ) (t :l Γ)
      = agree_ren (upren id) (t :l Γ) (t.[ren id] :l Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
    assert (agree_ren id (:n Γ) (:n Γ)
      = agree_ren (upren id) (:n Γ) (:n Γ))
      by autosubst.
    rewrite H.
    constructor; eauto.
Qed.

Lemma agree_ren_pure Γ Γ' xi :
  agree_ren xi Γ Γ' ->
  pure Γ ->
  pure Γ'.
Proof.
  induction 1; simpl; intros; eauto.
  - inv H0; eauto.
    constructor; eauto.
  - inv H0.
  - inv H0; subst; eauto.
    constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma agree_ren_re_re Γ Γ' xi :
  agree_ren xi Γ Γ' ->
  agree_ren xi (re Γ) (re Γ').
Proof.
  induction 1; simpl; constructor; eauto.
Qed.

Lemma agree_ren_hasU Γ Γ' xi :
  agree_ren xi Γ Γ' ->
  forall x A,
    hasU Γ x A ->
    hasU Γ' (xi x) A.[ren xi].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    eapply agree_ren_pure; eauto.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H.
  - inv H; subst.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
Qed.

Lemma agree_ren_hasL Γ Γ' xi :
  agree_ren xi Γ Γ' ->
  forall x A,
    hasL Γ x A ->
    hasL Γ' (xi x) A.[ren xi].
Proof.
  intro H2.
  dependent induction H2; simpl; intros; eauto.
  - inv H.
  - destruct x; asimpl.
    inv H.
    inv H; subst.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    eapply agree_ren_pure; eauto.
  - inv H.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
  - replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply IHagree_ren; eauto.
Qed.

Lemma merge_agree_ren_inv Γ Γ' xi :
  agree_ren xi Γ Γ' ->
  forall Γ1 Γ2,
    merge Γ1 Γ2 Γ ->
    exists Γ1' Γ2',
      merge Γ1' Γ2' Γ' /\
      agree_ren xi Γ1 Γ1' /\
      agree_ren xi Γ2 Γ2'.
Proof.
  induction 1; intros.
  - inv H.
    exists nil.
    exists nil.
    repeat constructor.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren xi] :u x).
    exists (m.[ren xi] :u x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (m.[ren xi] :l x).
    exists (:n x0).
    repeat constructor; eauto.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (:n x).
    exists (m.[ren xi] :l x0).
    repeat constructor; eauto.
  - inv H0; subst.
    pose proof (IHagree_ren _ _ H4).
    first_order.
    exists (:n x).
    exists (:n x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (m :u x).
    exists (m :u x0).
    repeat constructor; eauto.
  - pose proof (IHagree_ren _ _ H0).
    first_order.
    exists (:n x).
    exists (:n x0).
    repeat constructor; eauto.
Qed.

Lemma rename_ok Γ m A s :
  [ Γ |- m :- A -: s ] ->
  forall Γ' xi,
    agree_ren xi Γ Γ' ->
    [ Γ' |- m.[ren xi] :- A.[ren xi] -: s ].
Proof.
  intros H.
  induction H; simpl; intros.
  - pose proof (agree_ren_pure H0 H).
    apply p_axiom; assumption.
  - pose proof (agree_ren_pure H0 H).
    apply s_axiom; assumption.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    eapply u_prop; eauto.
    replace (prop U) with ((prop U).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply u_prod; eauto.
    replace (s @ l) with ((s @ l).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - asimpl.
    pose proof (agree_ren_pure H2 H).
    apply l_prod; eauto.
    replace (s @ l) with ((s @ l).[ren (upren xi)]) by autosubst.
    apply IHhas_type2.
    constructor; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply u_var.
    eapply agree_ren_hasU; eauto.
  - replace (ids (xi x)) with (Var (xi x)) by autosubst.
    apply l_var.
    eapply agree_ren_hasL; eauto.
  - eapply u_lam.
    eapply agree_ren_pure; eauto.
    apply IHhas_type1; eauto.
    asimpl.
    apply IHhas_type2; eauto.
    destruct s; constructor; eauto.
  - eapply l_lam.
    apply IHhas_type1; eauto.
    apply agree_ren_re_re; eauto.
    asimpl.
    apply IHhas_type2.
    destruct s; constructor; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H3 H2).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    pose proof (agree_ren_pure H6 H).
    eapply u_app; eauto.
  - asimpl.
    pose proof (merge_agree_ren_inv H2 H1).
    first_order. asimpl in IHhas_type1.
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    eapply l_app; eauto.
  - eapply conversion.
    apply sub_ren; eauto.
    apply IHhas_type1.
    apply agree_ren_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma hasU_ok Γ :
  [ Γ |- ] ->
  forall x A,
    hasU Γ x A ->
    exists l, [ re Γ |- A :- Sort U l -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    exists l.
    replace (Sort U l) with ((Sort U l).[ren (+1)]) by autosubst.
    eapply rename_ok.
    apply H0.
    apply agree_ren_wkU.
    rewrite <- pure_re; eauto.
    apply agree_ren_refl.
    specialize (IHcontext_ok _ _ H6).
    inv IHcontext_ok.
    exists x.
    replace (Sort U x) with ((Sort U x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkU.
    apply agree_ren_refl.
  - inv H1.
  - inv H0.
    specialize (IHcontext_ok _ _ H2).
    inv IHcontext_ok.
    exists x.
    replace (Sort U x) with ((Sort U x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma hasL_ok Γ :
  [ Γ |- ] ->
  forall x A,
    hasL Γ x A ->
    exists l, [ re Γ |- A :- Sort L l -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; simpl.
    specialize (IHcontext_ok _ _ H6).
    inv IHcontext_ok.
    exists x.
    replace (Sort L x) with ((Sort L x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkU.
    apply agree_ren_refl.
  - inv H1; simpl.
    exists l.
    replace (Sort L l) with ((Sort L l).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
  - inv H0; simpl.
    specialize (IHcontext_ok _ _ H2).
    inv IHcontext_ok.
    exists x.
    replace (Sort L x) with ((Sort L x).[ren (+1)]) by autosubst.
    eapply rename_ok; eauto.
    apply agree_ren_wkN.
    apply agree_ren_refl.
Qed.

Lemma weakeningU Γ m A s B :
  [ Γ |- m :- A -: s ] ->
  [ B :u Γ |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkU.
  apply agree_ren_refl.
Qed.

Lemma weakeningN Γ m A s :
  [ Γ |- m :- A -: s ] ->
  [ :n Γ |- m.[ren (+1)] :- A.[ren (+1)] -: s ].
Proof.
  intros.
  eapply rename_ok in H.
  apply H.
  apply agree_ren_wkN.
  apply agree_ren_refl.
Qed.

Lemma eweakeningU Γ m m' A A' s B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Γ |- m :- A -: s ] -> 
  [ B :u Γ |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakeningU; eauto.
Qed.

Lemma eweakeningN Γ m m' A A' s :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Γ |- m :- A -: s ] -> 
  [ :n Γ |- m' :- A' -: s ].
Proof.  
  intros; subst.
  apply weakeningN; eauto.
Qed.

Reserved Notation "[ Delta |- σ -| Γ ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil σ :
  [ nil |- σ -| nil ]
| agree_subst_u Delta σ Γ A :
  [ Delta |- σ -| Γ ] ->
  [ A.[σ] :u Delta |- up σ -| A :u Γ ]
| agree_subst_l Delta σ Γ A :
  [ Delta |- σ -| Γ ] ->
  [ A.[σ] :l Delta |- up σ -| A :l Γ ]
| agree_subst_n Delta σ Γ :
  [ Delta |- σ -| Γ ] ->
  [ :n Delta |- up σ -| :n Γ ]
| agree_subst_wkU Delta σ Γ n A :
  [ Delta |- σ -| Γ ] ->
  [ re Delta |- n :- A.[σ] -: U ] ->
  [ Delta |- n .: σ -| A :u Γ ]
| agree_subst_wkL Delta1 Delta2 Delta σ Γ n A :
  merge Delta1 Delta2 Delta ->
  [ Delta1 |- σ -| Γ ] ->
  [ Delta2 |- n :- A.[σ] -: L ] ->
  [ Delta |- n .: σ -| A :l Γ ]
| agree_subst_wkN Delta σ Γ n :
  [ Delta |- σ -| Γ ] ->
  [ Delta |- n .: σ -| :n Γ ]
| agree_subst_convU Delta σ Γ A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[σ] :- Sort U l -: U ] ->
  [ Delta |- σ -| A :u Γ ] ->
  [ Delta |- σ -| B :u Γ ]
| agree_subst_convL Delta σ Γ A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[σ] :- Sort L l -: U ] ->
  [ re Γ |- B :- Sort L l -: U ] ->
  [ Delta |- σ -| A :l Γ ] ->
  [ Delta |- σ -| B :l Γ ]
where "[ Delta |- σ -| Γ ]" := (agree_subst Delta σ Γ).

Lemma agree_subst_pure Delta σ Γ :
  [ Delta |- σ -| Γ ] -> pure Γ -> pure Delta.
Proof.
  induction 1; intros; eauto.
  inv H0.
  constructor; eauto.
  inv H0.
  inv H0.
  constructor; eauto.
  inv H1; eauto.
  inv H2.
  inv H0; eauto.
  inv H2.
  apply IHagree_subst.
  constructor; eauto.
  inv H3.
Qed.

Lemma agree_subst_refl Γ :
  [ Γ |- ids -| Γ ].
Proof.
  induction Γ.
  - constructor.
  - destruct a.
    destruct p.
    destruct s.
    replace ([t :u Γ |- ids -| t :u Γ])
      with ([t.[ids] :u Γ |- up ids -| t :u Γ])
      by autosubst.
    apply agree_subst_u; eauto.
    replace ([t :l Γ |- ids -| t :l Γ])
      with ([t.[ids] :l Γ |- up ids -| t :l Γ])
      by autosubst.
    apply agree_subst_l; eauto.
    replace (ids) with (up ids) by autosubst.
    apply agree_subst_n; eauto.
Qed.

Lemma agree_subst_hasU Delta σ Γ :
  [ Delta |- σ -| Γ ] ->
  forall x A,
    hasU Γ x A -> 
    [ Delta |- σ x :- A.[σ] -: U ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H0.
    + asimpl.
      apply u_var.
      replace (A.[σ >> ren (+1)]) 
        with (A.[σ].[ren (+1)]) by autosubst.
      constructor.
      eapply agree_subst_pure; eauto.
    + eapply eweakeningU; eauto.
      autosubst.
      autosubst.
  - inv H0.
  - inv H0.
    eapply eweakeningN; eauto.
    autosubst.
    autosubst.
  - inv H1; asimpl; eauto.
    pose proof (agree_subst_pure H H6).
    pose proof (pure_re H1).
    rewrite H2; eauto.
  - inv H2.
  - inv H0; asimpl; eauto.
  - inv H2.
    + assert (hasU (A :u Γ) 0 A.[ren (+1)]).
      constructor; eauto.
      eapply conversion.
      eapply sub_subst.
      eapply sub_ren; eauto.
      apply H0.
      apply IHagree_subst; eauto.
    + eapply IHagree_subst.
      constructor; eauto.
  - inv H3.
Qed.

Lemma agree_subst_hasL Delta σ Γ :
  [ Delta |- σ -| Γ ] ->
  forall x A,
    hasL Γ x A -> 
    [ Delta |- σ x :- A.[σ] -: L ].
Proof.
  induction 1; intros.
  - inv H.
  - inv H0.
    eapply eweakeningU; eauto.
    autosubst.
    autosubst.
  - inv H0.
    asimpl.
    replace (A.[σ >> ren (+1)]) 
      with (A.[σ].[ren (+1)]) by autosubst.
    constructor.
    constructor.
    eapply agree_subst_pure; eauto.
  - inv H0.
    eapply eweakeningN; eauto.
    autosubst.
    autosubst.
  - inv H1; asimpl; eauto.
  - inv H2; asimpl.
    pose proof (agree_subst_pure H0 H7).
    pose proof (merge_pure1 H H2).
    rewrite H3; eauto.
  - inv H0; asimpl; eauto.
  - inv H2.
    apply IHagree_subst.
    constructor; eauto.
  - inv H3.
    assert (hasL (A :l Γ) 0 A.[ren (+1)]).
    constructor; eauto.
    eapply conversion.
    apply sub_subst.
    apply sub_ren; eauto.
    apply H0.
    apply IHagree_subst; eauto.
Qed.

Lemma agree_subst_re_re Delta σ Γ :
  [ Delta |- σ -| Γ ] ->
  [ re Delta |- σ -| re Γ ].
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
    rewrite <- re_re; eauto.
  - constructor; eauto.
    pose proof (merge_re_re H).
    destruct H2.
    rewrite <- H2; eauto.
  - constructor; eauto.
  - simpl in IHagree_subst.
    eapply agree_subst_convU.
    apply H.
    rewrite <- re_re.
    apply H0.
    apply IHagree_subst.
Qed.

Lemma merge_agree_subst_inv Delta σ Γ :
  [ Delta |- σ -| Γ ] ->
  forall Γ1 Γ2,
    merge Γ1 Γ2 Γ ->
    exists Delta1 Delta2,
      merge Delta1 Delta2 Delta /\
      [ Delta1 |- σ -| Γ1 ] /\
      [ Delta2 |- σ -| Γ2 ].
Proof.
  intros H.
  dependent induction H; intros.
  - inv H.
    exists nil.
    exists nil.
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (A.[σ] :u x).
    exists (A.[σ] :u x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (A.[σ] :l x).
    exists (:n x0).
    repeat constructor; eauto.
  - pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (:n x).
    exists (A.[σ] :l x0).
    repeat constructor; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists (:n x).
    exists (:n x0).
    repeat constructor; eauto.
  - inv H1.
    pose proof (IHagree_subst _ _ H5).
    first_order.
    exists x.
    exists x0.
    pose proof (merge_re_re H1).
    destruct H4.
    repeat constructor; eauto.
    rewrite H4; eauto.
    rewrite H6; eauto.
  - inv H2.
    + pose proof (IHagree_subst _ _ H6).
      firstorder.
      pose proof (merge_split1 H H2).
      firstorder.
      exists x1.
      exists x0.
      firstorder.
      eapply agree_subst_wkL; eauto.
      eapply agree_subst_wkN; eauto.
    + pose proof (IHagree_subst _ _ H6).
      firstorder.
      pose proof (merge_split2 H H2).
      firstorder.
      exists x.
      exists x1.
      firstorder.
      apply agree_subst_wkN; eauto.
      eapply agree_subst_wkL; eauto.
  - inv H0.
    pose proof (IHagree_subst _ _ H4).
    first_order.
    exists x.
    exists x0.
    repeat constructor; eauto.
  - inv H2.
    assert (merge (A :u Γ0) (A :u Γ3) (A :u Γ)).
    apply merge_left; eauto.
    specialize (IHagree_subst _ _ H2).
    first_order.
    exists x.
    exists x0.
    pose proof (merge_re_re H3).
    inv H7.
    repeat constructor; eauto.
    eapply agree_subst_convU; eauto.
    rewrite H8; eauto.
    eapply agree_subst_convU; eauto.
    rewrite H9; eauto.
  - inv H3.
    + assert (merge (A :l Γ0) (:n Γ3) (A :l Γ)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H3).
      first_order.
      exists x.
      exists x0.
      pose proof (merge_re_re H4). inv H8.
      pose proof (merge_re_re H7). inv H8.
      repeat constructor; eauto.
      eapply agree_subst_convL; eauto.
      rewrite H9; eauto.
      rewrite H11; eauto.
    + assert (merge (:n Γ0) (A :l Γ3) (A :l Γ)).
      constructor; eauto.
      specialize (IHagree_subst _ _ H3).
      first_order.
      exists x.
      exists x0.
      pose proof (merge_re_re H4). inv H8.
      pose proof (merge_re_re H7). inv H8.
      repeat constructor; eauto.
      eapply agree_subst_convL; eauto.
      rewrite H10; eauto.
      rewrite H12; eauto.
Qed.

Lemma substitution Γ m A s :
  [ Γ |- m :- A -: s ] ->
  forall Delta σ,
    [ Delta |- σ -| Γ ] ->
    [ Delta |- m.[σ] :- A.[σ] -: s ].
Proof.
  intros H.
  dependent induction H; asimpl; intros; eauto.
  - apply p_axiom.
    eapply agree_subst_pure; eauto.
  - apply s_axiom.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    eapply u_prop; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_u A H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply u_prod; eauto.
    eapply agree_subst_pure; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    pose proof (agree_subst_n H2).
    specialize (IHhas_type2 _ _ H3). asimpl in IHhas_type2.
    apply l_prod; eauto.
    eapply agree_subst_pure; eauto.
  - eapply agree_subst_hasU; eauto.
  - eapply agree_subst_hasL; eauto.
  - specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    destruct s.
    + pose proof (agree_subst_u A H2).
      specialize (IHhas_type2 _ _ H3).
      eapply u_lam; eauto.
      eapply agree_subst_pure; eauto.
    + pose proof (agree_subst_l A H2).
      specialize (IHhas_type2 _ _ H3).
      eapply u_lam; eauto.
      eapply agree_subst_pure; eauto.
  - pose proof (agree_subst_re_re H1).
    specialize (IHhas_type1 _ _ H2). asimpl in IHhas_type1.
    destruct s.
    + pose proof (agree_subst_u A H1).
      specialize (IHhas_type2 _ _ H3).
      eapply l_lam; eauto.
    + pose proof (agree_subst_l A H1).
      specialize (IHhas_type2 _ _ H3).
      eapply l_lam; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H3 H2).
    first_order.
    pose proof (agree_subst_pure H6 H).
    pose proof (u_app H7 IHhas_type1 IHhas_type2 H4).
    asimpl in H8; eauto.
  - asimpl.
    pose proof (merge_agree_subst_inv H2 H1).
    first_order.
    pose proof (l_app IHhas_type1 IHhas_type2 H3).
    asimpl in H6; eauto.
  - eapply conversion.
    apply sub_subst; eauto.
    apply IHhas_type1; eauto.
    apply agree_subst_re_re; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma substitutionU Γ1 m A B s :
  [ A :u Γ1 |- m :- B -: s ] ->
  forall Γ2 Γ n,
    pure Γ2 ->
    merge Γ1 Γ2 Γ -> 
    [ Γ2 |- n :- A -: U ] -> 
    [ Γ |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  pose proof (merge_pure2 H1 H0).
  rewrite H3.
  apply agree_subst_wkU; eauto.
  apply agree_subst_refl.
  pose proof (merge_re_re H1).
  destruct H4.
  asimpl.
  rewrite H4.
  rewrite <- H5.
  rewrite <- pure_re; eauto.
Qed.

Lemma substitutionN Γ1 m A B s :
  [ :n Γ1 |- m :- B -: s ] ->
  forall Γ2 n t,
    [ Γ2 |- n :- A -: t ] -> 
    [ Γ1 |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  apply agree_subst_wkN; eauto.
  apply agree_subst_refl.
Qed.

Lemma substitutionL Γ1 m A B s :
  [ A :l Γ1 |- m :- B -: s ] ->
  forall Γ2 Γ n,
    merge Γ1 Γ2 Γ -> 
    [ Γ2 |- n :- A -: L ] -> 
    [ Γ |- m.[n/] :- B.[n/] -: s ].
Proof.
  intros.
  eapply substitution.
  apply H.
  eapply agree_subst_wkL; asimpl; eauto.
  apply agree_subst_refl.
Qed.

Lemma context_convU Γ m A B C s l :
  B === A -> 
  [ re Γ |- A :- Sort U l -: U ] ->
  [ A :u Γ |- m :- C -: s ] -> 
  [ B :u Γ |- m :- C -: s ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B :u Γ |- m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp2.
  eapply agree_subst_convU; simpl.
  eapply conv_sub; eauto.
  pose proof (weakeningU B tp1).
  asimpl.
  asimpl in H.
  apply H.
  apply agree_subst_refl.
Qed.

Lemma context_convL Γ m A B C s l :
  B === A -> 
  [ re Γ |- A :- Sort L l -: U ] ->
  [ A :l Γ |- m :- C -: s ] -> 
  [ B :l Γ |- m :- C -: s ].
Proof.
  move=> conv tp1 tp2. 
  cut ([ B :l Γ |- m.[ids] :- C.[ids] -: s ]). autosubst.
  eapply substitution.
  apply tp2.
  eapply agree_subst_convL; simpl.
  eapply conv_sub; eauto.
  pose proof (weakeningN tp1).
  asimpl.
  asimpl in H.
  apply H.
  apply tp1.
  apply agree_subst_refl.
Qed.

Ltac solve_sub :=
  match goal with
  | [ H : _ <: _ |- _ ] =>
    let A := fresh "A" in
    let B := fresh "B" in
    let sb := fresh "sb" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    destruct H as [A B sb c1 c2]; destruct sb
  end;
  match goal with
  | [ c1 : ?A === ?x, c2 : ?x === ?B |- _ ] => 
    assert (A === B) by 
      (eapply conv_trans; try solve [apply c1| apply c2]);
    clear c1 c2;
    solve_conv
  | _ => solve_conv
  end.

Lemma u_prod_inv Γ A B s srt :
  [ re Γ |- Prod A B U s :- srt -: U ] -> 
  exists l,
    [ re Γ |- A :- Sort U l -: U ] /\ 
    [ A :u re Γ |- B :- Sort s l -: U ].
Proof.
  move e:(Prod A B U s) => n tp. 
  elim: tp A B s e => //{Γ n srt}.
  - move=> Γ A B l p tp1 _ tp2 _ A0 B0 s [->->->].
    exists l; firstorder.
    destruct l; eauto.
    assert (prop U <: U @ n).
    apply sub_prop.
    eapply conversion; eauto.
    constructor; apply re_pure.
  - move=> Γ A B s _ l p tp1 _ pt2 _ A0 B0 s0 [->->->].
    exists (Some l); eauto.
Qed.

Lemma l_prod_inv Γ A B s srt :
  [ re Γ |- Prod A B L s :- srt -: U ] -> 
  exists l,
    [ re Γ |- A :- Sort L l -: U ] /\ 
    [ :n re Γ |- B :- Sort s l -: U ].
Proof.
  move e:(Prod A B L s) => n tp. 
  elim: tp A B s e => //{Γ n srt}.
  - move=> Γ A B s _ l p tp1 _ pt2 _ A0 B0 s0 [->->->].
    exists (Some l); eauto.
Qed.

Lemma l_prod_falseX Γ A B s srt :
  [ re Γ |- Prod A B L s :- srt -: U ] ->
  srt <: prop U -> False.
Proof.
  intro h.
  dependent induction h; intros.
  - exfalso; solve_sub.
  - eapply IHh2; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma l_prod_false Γ A B s :
  ~[ re Γ |- Prod A B L s :- prop U -: U ].
Proof.
  intro h.
  eapply l_prod_falseX; eauto.
Qed.

Lemma u_lam_invX Γ n C srt :
  [ Γ |- Lam n :- C -: srt ] -> 
  forall A B s l, 
    (C <: Prod A B U s /\ [A :u re Γ |- B :- Sort s l -: U]) ->
    [ A :u Γ |- n :- B -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  + pose proof (sub_prod_inv H2).
    first_order; subst.
    pose proof (pure_re H).
    rewrite H6 in H0.
    apply u_prod_inv in H0. inv H0.
    eapply conversion; eauto.
    eapply context_convU.
    apply conv_sym; apply H4.
    apply H7.
    apply H1.
  + pose proof (sub_prod_inv H1).
    first_order; subst.
    apply u_prod_inv in H. inv H.
    eapply conversion; eauto.
    eapply context_convU.
    apply conv_sym; apply H3.
    apply H5.
    apply H0.
  + eapply IHhas_type2; eauto.
    split.
    eapply sub_trans; eauto.
    apply H3.
Qed.

Lemma u_lam_inv Γ n A B s t l :
  [ re Γ |- Prod A B U s :- Sort t l -: U ] ->
  [ Γ |- Lam n :- Prod A B U s -: t ] -> 
  [ A :u Γ |- n :- B -: s ].
Proof.
  intros.
  apply u_prod_inv in H; inv H; firstorder.
  eapply u_lam_invX; eauto.
Qed.

Lemma l_lam_invX Γ n C srt :
  [ Γ |- Lam n :- C -: srt ] -> 
  forall A B s l, 
    (C <: Prod A B L s /\ [:n re Γ |- B :- Sort s l -: U]) ->
    [ A :l Γ |- n :- B -: s ].
Proof.
  intros.
  dependent induction H; firstorder.
  + pose proof (sub_prod_inv H2).
    first_order; subst.
    pose proof (pure_re H).
    rewrite H6 in H0.
    apply l_prod_inv in H0. inv H0.
    eapply conversion; eauto.
    eapply context_convL.
    apply conv_sym; apply H4.
    apply H7.
    apply H1.
  + pose proof (sub_prod_inv H1).
    first_order; subst.
    apply l_prod_inv in H. inv H.
    eapply conversion; eauto.
    eapply context_convL.
    apply conv_sym; apply H3.
    apply H5.
    apply H0.
  + eapply IHhas_type2; eauto.
    split.
    eapply sub_trans; eauto.
    apply H3.
Qed.

Lemma l_lam_inv Γ n A B s t l :
  [ re Γ |- Prod A B L s :- Sort t l -: U ] ->
  [ Γ |- Lam n :- Prod A B L s -: t ] -> 
  [ A :l Γ |- n :- B -: s ].
Proof.
  intros.
  apply l_prod_inv in H; inv H; firstorder.
  eapply l_lam_invX; eauto.
Qed.

Lemma merge_context_ok_inv Γ Γ1 Γ2 :
  merge Γ1 Γ2 Γ ->
  [ Γ |- ] ->
  [ Γ1 |- ] /\ [ Γ2 |- ].
Proof.
  induction 1; intros.
  - repeat constructor.
  - inv H0.
    apply IHmerge in H3.
    apply merge_re_re in H. inv H.
    inv H3. split.
    eapply u_ok; eauto.
    rewrite H0; eauto.
    eapply u_ok; eauto.
    rewrite H1; eauto.
  - inv H0.
    apply IHmerge in H3.
    apply merge_re_re in H. inv H.
    inv H3; split.
    eapply l_ok; eauto.
    rewrite H0; eauto.
    constructor; eauto.
  - inv H0.
    apply IHmerge in H3.
    apply merge_re_re in H. inv H.
    inv H3; split.
    constructor; eauto.
    eapply l_ok; eauto.
    rewrite H1; eauto.
  - inv H0.
    apply IHmerge in H2.
    apply merge_re_re in H. inv H.
    inv H2; split; constructor; eauto.
Qed.

Theorem propagation Γ m A s : 
  [ Γ |- ] ->
  [ Γ |- m :- A -: s ] ->
  exists l, [ re Γ |- A :- Sort s l -: U ].
Proof.
  intros.
  dependent induction H0.
  - exists (Some 1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some l.+2).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some 0).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - exists (Some l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  - eapply hasU_ok; eauto.
  - eapply hasL_ok; eauto.
  - exists l.
    rewrite <- pure_re; eauto.
  - exists (Some l); eauto.
  - pose proof (merge_pure2 H1 H0).
    pose proof (merge_re_re H1). inv H3.
    apply merge_context_ok_inv in H1; eauto. inv H1.
    apply IHhas_type1 in H2. inv H2.
    apply u_prod_inv in H1. first_order.
    exists x0.
    replace (Sort s x0) with ((Sort s x0).[n/]) by autosubst.
    eapply substitutionU; eauto.
    replace (Γ2) with (re Γ1).
    apply merge_re_re_re.
    apply pure_re in H0.
    rewrite H0.
    rewrite H5; eauto.
  - pose proof (merge_re_re H0). inv H1.
    apply merge_context_ok_inv in H0; eauto. inv H0.
    apply IHhas_type1 in H1. inv H1.
    eapply l_prod_inv in H0; eauto; inv H0.
    exists x0.
    replace (Sort s x0) with ((Sort s x0).[n/]) by autosubst.
    eapply substitutionN; eauto.
    rewrite <- H2.
    apply H1.
  - exists l; eauto.
Qed.

Lemma propL_false Γ A :
  ~[ Γ |- prop L :- A -: U ].
Proof.
  intro H.
  dependent induction H.
  apply IHhas_type2; eauto.
Qed.

Lemma has_propL_false Γ m s :
  [ Γ |- ] -> [ Γ |- m :- prop L -: s ] -> False.
Proof.
  intros.
  apply propagation in H0; eauto.
  inv H0.
  apply propL_false in H1; eauto.
Qed.

Theorem subject_reduction Γ m A s :
  [ Γ |- ] ->
  [ Γ |- m :- A -: s ] ->
  forall n, pstep m n -> 
    [ Γ |- n :- A -: s ].
Proof.
  intros.
  dependent induction H0.
  - inv H1.
    apply p_axiom; eauto.
  - inv H1.
    apply s_axiom; eauto.
  - inv H1.
    assert ([A :u Γ |-]).
    eapply u_ok; eauto.
    rewrite <-pure_re; eauto.
    specialize (IHhas_type1 H _ H7).
    specialize (IHhas_type2 H1 _ H8).
    eapply u_prop; eauto.
    eapply context_convU.
    eapply conv1i; eauto.
    rewrite <- pure_re; eauto.
    apply IHhas_type2.
  - inv H1.
    assert ([A :u Γ |-]).
    eapply u_ok; eauto.
    rewrite <-pure_re; eauto.
    specialize (IHhas_type1 H _ H7).
    specialize (IHhas_type2 H1 _ H8).
    apply u_prod; eauto.
    eapply context_convU.
    eapply conv1i; eauto.
    rewrite <- pure_re; eauto.
    apply IHhas_type2.
  - inv H1.
    assert ([:n Γ |-]).
    eapply n_ok; eauto.
    specialize (IHhas_type1 H _ H7).
    specialize (IHhas_type2 H1 _ H8).
    apply l_prod; eauto.
  - inv H1.
    apply u_var; eauto.
  - inv H1.
    apply l_var; eauto.
  - inv H1.
    pose proof (pure_re H0).
    pose proof H0_.
    rewrite H1 in H0_.
    destruct s.
    + apply u_prod_inv in H0_. first_order.
      assert ([A :u Γ |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H6 _ H3).
      eapply u_lam; eauto.
    + apply l_prod_inv in H0_. first_order.
      assert ([A :l Γ |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H6 _ H3).
      eapply u_lam; eauto.
  - inv H1.
    pose proof H0_.
    destruct s.
    + apply u_prod_inv in H0_. first_order.
      assert ([A :u Γ |-]).
      eapply u_ok; eauto.
      specialize (IHhas_type2 H4 _ H2).
      eapply l_lam; eauto.
    + apply l_prod_inv in H0_. first_order.
      assert ([A :l Γ |-]).
      eapply l_ok; eauto.
      specialize (IHhas_type2 H4 _ H2).
      eapply l_lam; eauto.
  - pose proof (merge_context_ok_inv H1 H). inv H3.
    inv H2.
    + specialize (IHhas_type1 H4 _ H7).
      specialize (IHhas_type2 H5 _ H9).
      pose proof (propagation H4 IHhas_type1). inv H2.
      apply u_prod_inv in H3. inv H3.
      pose proof (merge_re_re H1). first_order.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H11.
      assert ([re Γ |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0).
      rewrite H12. rewrite H3. rewrite H6.
      apply merge_re_re_re.
      eapply conversion; eauto.
      eapply u_app; eauto.
    + assert (pstep (Lam m0) (Lam m')). 
      constructor; eauto.
      specialize (IHhas_type1 H4 _ H2).
      specialize (IHhas_type2 H5 _ H9).
      pose proof (propagation H4 IHhas_type1). inv H3.
      pose proof (u_prod_inv H6). first_order.
      pose proof (merge_re_re H1). inv H10.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H13.
      assert ([re Γ |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionU; eauto.
      pose proof (pure_re H0); eauto.
      rewrite H14. rewrite H11. rewrite H12.
      apply merge_re_re_re.
      eapply u_lam_inv in IHhas_type1; eauto.
      eapply conversion; eauto.
      eapply substitutionU; eauto.
  - pose proof (merge_context_ok_inv H0 H). inv H2.
    inv H1.
    + specialize (IHhas_type1 H3 _ H6).
      specialize (IHhas_type2 H4 _ H8).
      pose proof (propagation H3 IHhas_type1). inv H1.
      apply l_prod_inv in H2. inv H2.
      pose proof (merge_re_re H0). inv H2.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H9.
      assert ([re Γ |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionN; eauto.
      rewrite <-H5.
      apply H1.
      eapply conversion; eauto.
      eapply l_app; eauto.
    + assert (pstep (Lam m0) (Lam m')). 
      constructor; eauto.
      specialize (IHhas_type1 H3 _ H1).
      specialize (IHhas_type2 H4 _ H8).
      pose proof (propagation H3 IHhas_type1). inv H2.
      pose proof (l_prod_inv H5). inv H2.
      pose proof (merge_re_re H0). inv H2.
      assert (pstep B.[n/] B.[n'/]).
      apply pstep_compat_beta; eauto using pstep_refl.
      assert (B.[n'/] === B.[n/]).
      apply conv1i; eauto.
      apply conv_sub in H11.
      assert ([re Γ |- B.[n/] :- (Sort s x0).[n/] -: U ]).
      eapply substitutionN; eauto.
      rewrite <- H9.
      apply H7.
      eapply l_lam_inv in IHhas_type1; eauto.
      eapply conversion; eauto.
      eapply substitutionL; eauto.
  - eapply conversion; eauto.
Qed.

Corollary preservation_step m n :
  step m n ->
  forall Γ A s,
    [ Γ |- ] ->
    [ Γ |- m :- A -: s ] ->
    [ Γ |- n :- A -: s ].
Proof.
  intros.
  eapply preservation; eauto.
  apply step_pstep; eauto.
Qed.

Corollary preservation_star_step m n :
  star step m n ->
  forall Γ A s,
    [ Γ |- ] ->
    [ Γ |- m :- A -: s ] ->
    [ Γ |- n :- A -: s ].
Proof.
  intro H.
  dependent induction H; intros; eauto.
  eapply preservation.
  apply H1.
  apply IHstar; eauto.
  apply step_pstep; eauto.
Qed.

Lemma canonical_prod m C srt :
  [ nil |- m :- C -: srt ] -> value m ->
  forall A B s t, 
    C <: Prod A B s t -> exists m', m = Lam m'.
Proof.
  intros.
  dependent induction H; try (exfalso; solve_sub).
  - inv H.
  - inv H.
  - exists n; eauto.
  - exists n; eauto.
  - eapply IHhas_type2; eauto.
    eapply sub_trans; eauto.
Qed.

Theorem progress m A s :
  [ nil |- m :- A -: s ] -> value m \/ exists n, step m n.
Proof.
  intros.
  dependent induction H; try solve [left; constructor].
  - right.
    inv H2.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H2).
    specialize (IHhas_type2 H2).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_prod; eauto.
      destruct H5; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H4.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H3.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H3.
      exists (App x n).
      apply step_appL; eauto.
  - right.
    inv H1.
    assert (@nil (elem term) ~= @nil (elem term)) by eauto.
    specialize (IHhas_type1 H1).
    specialize (IHhas_type2 H1).
    destruct IHhas_type1; destruct IHhas_type2.
    + assert (exists m', m = Lam m').
      eapply canonical_prod; eauto.
      destruct H4; subst.
      exists (x.[n/]).
      apply step_beta; eauto.
    + destruct H3.
      exists (App m x).
      apply step_appR; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
    + destruct H2.
      exists (App x n).
      apply step_appL; eauto.
  - apply IHhas_type2; eauto.
Qed.

Inductive isL : context term -> nat -> Prop :=
| isL_O Γ A :
  isL (A :l Γ) 0
| isL_S Γ i A s :
  isL Γ i ->
  isL (A :[s] Γ) (i.+1)
| isL_N Γ i :
  isL Γ i ->
  isL (:n Γ) (i.+1).

Inductive isN : context term -> nat -> Prop :=
| isN_O Γ :
  isN (:n Γ) 0
| isN_S Γ i A s :
  isN Γ i ->
  isN (A :[s] Γ) (i.+1)
| isN_N Γ i :
  isN Γ i ->
  isN (:n Γ) (i.+1).

Fixpoint occurs (i : nat) (m : term) : nat :=
  match m with
  | Var x => if x == i then 1 else 0
  | Sort _ _ => 0
  | Prod A B _ _ => occurs i A + occurs (i.+1) B
  | Lam m => occurs (i.+1) m
  | App m n => occurs i m + occurs i n
  end.

Lemma eqn_refl (n : nat) : n == n.
Proof.
  induction n; simpl; eauto.
Qed.

Lemma isL_pure Γ i : isL Γ i -> ~pure Γ.
Proof.
  induction 1; unfold not; intros.
  inv H.
  destruct s.
  inv H0. firstorder.
  inv H0.
  inv H0. firstorder.
Qed.

Lemma isL_hasU Γ i : 
  isL Γ i -> forall x A, ~hasU Γ x A.
Proof.
  induction 1; intros; unfold not; intros.
  inv H.
  destruct s.
  inv H0. exfalso. eapply isL_pure; eauto.
  firstorder.
  inv H0.
  inv H0.
  firstorder.
Qed.

Lemma isL_hasL Γ i :
  isL Γ i -> forall x A, hasL Γ x A -> x = i.
Proof.
  induction 1; intros.
  inv H; eauto.
  destruct s.
  inv H0.
  pose proof (IHisL _ _ H5); eauto.
  inv H0; eauto.
  exfalso. eapply isL_pure; eauto.
  inv H0.
  pose proof (IHisL _ _ H2); eauto.
Qed.

Lemma isN_hasU Γ i :
  isN Γ i -> forall x A, hasU Γ x A -> x == i = false.
Proof.
  induction 1; intros; eauto.
  inv H; eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H6); eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H2); eauto.
Qed.

Lemma isN_hasL Γ i :
  isN Γ i -> forall x A, hasL Γ x A -> x == i = false.
Proof.
  induction 1; intros; eauto.
  inv H; eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H6); eauto.
  inv H0; eauto.
  pose proof (IHisN _ _ H2); eauto.
Qed.

Lemma isL_merge_inv Γ1 Γ2 Γ :
  merge Γ1 Γ2 Γ -> 
    forall i, isL Γ i -> 
      (isL Γ1 i /\ isN Γ2 i) \/
      (isL Γ2 i /\ isN Γ1 i).
Proof.
  intro H.
  dependent induction H; intros.
  - inv H.
  - inv H0.
    apply IHmerge in H5.
    firstorder.
    + left; repeat constructor; eauto.
    + right; repeat constructor; eauto.
  - inv H0.
    + left; repeat constructor; eauto.
    + apply IHmerge in H5.
      inv H5.
      * left; inv H0; repeat constructor; eauto.
      * right; inv H0; repeat constructor; eauto.
  - inv H0.
    + right; repeat constructor; eauto.
    + apply IHmerge in H5.
      firstorder.
      * left; repeat constructor; eauto.
      * right; repeat constructor; eauto.
  - inv H0.
    apply IHmerge in H2.
    firstorder.
    + left; repeat constructor; eauto.
    + right; repeat constructor; eauto.
Qed.

Lemma isN_merge_inv Γ1 Γ2 Γ :
  merge Γ1 Γ2 Γ -> 
    forall i, isN Γ i -> 
      isN Γ1 i /\ isN Γ2 i.
Proof.
  intro H.
  dependent induction H; intros.
  - inv H.
  - inv H0.
    apply IHmerge in H5.
    firstorder; constructor; eauto.
  - inv H0.
    apply IHmerge in H5.
    firstorder; constructor; eauto.
  - inv H0.
    apply IHmerge in H5.
    firstorder; constructor; eauto.
  - inv H0; firstorder; constructor; firstorder.
Qed.

Lemma narity Γ m A s :
  [ Γ |- m :- A -: s ] -> 
    forall i, isN Γ i -> occurs i m = 0.
Proof.
  intro H.
  dependent induction H; simpl; intros.
  - eauto.
  - eauto.
  - rewrite IHhas_type1; eauto.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - rewrite IHhas_type1; eauto.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - rewrite IHhas_type1; eauto.
    rewrite IHhas_type2; eauto.
    constructor; eauto.
  - pose proof (isN_hasU H0 H).
    rewrite H1; eauto.
  - pose proof (isN_hasL H0 H).
    rewrite H1; eauto.
  - apply IHhas_type2.
    constructor; eauto.
  - apply IHhas_type2.
    constructor; eauto.
  - pose proof (isN_merge_inv H2 H3). inv H4.
    rewrite IHhas_type1; eauto.
  - pose proof (isN_merge_inv H1 H2). inv H3.
    rewrite IHhas_type1; eauto.
  - apply IHhas_type2; eauto.
Qed.

Theorem linearity Γ m A s :
  [ Γ |- m :- A -: s ] -> 
    forall i, isL Γ i -> occurs i m = 1.
Proof.
  intro H.
  dependent induction H; intros.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_pure; eauto.
  - exfalso. eapply isL_hasU; eauto.
  - pose proof (isL_hasL H0 H).
    rewrite H1; simpl.
    rewrite eqn_refl; eauto.
  - exfalso. eapply isL_pure; eauto.
  - simpl.
    apply IHhas_type2.
    constructor; eauto.
  - pose proof (isL_merge_inv H2 H3).
    firstorder; simpl.
    + apply IHhas_type1 in H4.
      eapply narity in H5; eauto.
      rewrite H4.
      rewrite H5.
      eauto.
    + apply IHhas_type2 in H4.
      eapply narity in H5; eauto.
      rewrite H4.
      rewrite H5.
      eauto.
  - pose proof (isL_merge_inv H1 H2).
    firstorder; simpl.
    + apply IHhas_type1 in H3.
      eapply narity in H4; eauto.
      rewrite H3.
      rewrite H4.
      eauto.
    + apply IHhas_type2 in H3.
      eapply narity in H4; eauto.
      rewrite H3.
      rewrite H4.
      eauto.
  - apply IHhas_type2; eauto.
Qed.

Close Scope clc_scope.

Import CC.

Fixpoint erase (m : CLC.term) : CC.term :=
  match m with
  | CLC.Var x => CC.Var x
  | CLC.Sort _ l => CC.Sort l
  | CLC.Prod A B _ _ => CC.Prod (erase A) (erase B)
  | CLC.Lam n => CC.Lam (erase n)
  | CLC.App m n => CC.App (erase m) (erase n)
  end.

Fixpoint erase_context 
  (Γ : CLC.context CLC.term) 
: CC.context CC.term :=
  match Γ with
  | Some (t, U) :: Γ => erase t :s erase_context Γ
  | Some (t, L) :: Γ => erase t :s erase_context Γ
  | None :: Γ => :n erase_context Γ
  | nil => nil
  end.

Notation "[| m |]" := (erase m).
Notation "[[ Γ ]]" := (erase_context Γ).

Lemma erase_value v : 
  CLC.value v <-> CC.value [|v|].
Proof.
  split.
  induction 1; simpl; constructor.
  induction v; simpl; try constructor.
  intros.
  inv H.
Qed.

Definition erase_subst 
  (σ : var -> CLC.term) 
  (τ : var -> CC.term)
: Prop := 
  forall x, [|σ x|] = τ x.

Lemma erase_ren_com m :
  forall xi, [| m |].[ren xi] = [| m.[ren xi] |].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm; eauto.
  - rewrite IHm1 IHm2; eauto.
Qed.

Lemma erase_subst_up σ τ :
  erase_subst σ τ -> erase_subst (up σ) (up τ).
Proof.
  unfold erase_subst.
  intros.
  induction x; asimpl; eauto.
  rewrite <-H.
  rewrite erase_ren_com; eauto.
Qed.

Lemma erase_subst_com m :
  forall σ τ, 
    erase_subst σ τ ->
    [| m.[σ] |] = [| m |].[τ].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite <- (IHm σ); eauto.
    rewrite <- (IHm0 (up σ)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm (up σ)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm1 σ); eauto.
    rewrite <- (IHm2 σ); eauto.
Qed.

Lemma erase_pstep m n :
  CLC.pstep m n -> CC.pstep [|m|] [|n|].
Proof with eauto using pstep, pstep_refl.
  induction 1; simpl; intros...
  erewrite erase_subst_com.
  eapply pstep_beta; eauto.
  unfold erase_subst; intros; destruct x; asimpl; eauto.
Qed.

Lemma erase_conv m n :
  conv CLC.pstep m n -> conv CC.pstep [|m|] [|n|].
Proof.
  induction 1; eauto.
  eapply conv_trans.
  apply IHconv.
  eapply convSE; eauto.
  apply erase_pstep; eauto.
  eapply convSEi; eauto.
  apply erase_pstep; eauto.
Qed.

Lemma erase_sub1 m n :
  CLC.sub1 m n -> CC.sub1 [|m|] [|n|].
Proof.
  induction 1; asimpl; eauto using sub1.
Qed.

Lemma erase_sub m n :
  CLC.sub m n -> CC.sub [|m|] [|n|].
Proof.
  move=> [A B sb] c1 c2.
  inv sb.
  - assert (conv CLC.pstep m n).
    eapply conv_trans.
    apply c1.
    apply c2.
    apply erase_conv in H.
    apply conv_sub; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    assert (sub1 (prop) (@l)).
    constructor; eauto.
    apply sub1_sub in H.
    eapply sub_trans. eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    assert (sub1 (@l1) (@l2)).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
  - apply erase_conv in c1. simpl in c1.
    apply erase_conv in c2. simpl in c2.
    apply conv_sub in c1.
    apply conv_sub in c2.
    apply erase_sub1 in H.
    assert (sub1 (Prod [|A0|] [|B1|]) (Prod [|A0|] [|B2|])).
    constructor; eauto.
    apply sub1_sub in H0.
    eapply sub_trans; eauto.
    eapply sub_trans; eauto.
Qed.

Lemma hasU_erase Γ x A :
  hasU Γ x A -> has [[ Γ ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Lemma hasL_erase Γ x A :
  hasL Γ x A -> has [[ Γ ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Inductive agree_wk : 
  CC.context CC.term -> CC.context CC.term -> Prop :=
| agree_wk_nil : agree_wk nil nil
| agree_wk_s Γ1 Γ2 e :
  agree_wk Γ1 Γ2 ->
  agree_wk (e :: Γ1) (e :: Γ2)
| agree_wk_n Γ1 Γ2 A :
  agree_wk Γ1 Γ2 ->
  agree_wk (:n Γ1) (A :s Γ2).

Lemma agree_wk_refl Γ : agree_wk Γ Γ.
Proof.
  induction Γ.
  - constructor.
  - constructor; eauto.
Qed.

Lemma agree_wk_has Γ1 Γ2 :
  agree_wk Γ1 Γ2 ->
  forall x A,
    has Γ1 x A ->
    has Γ2 x A.
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  inv H0; constructor; eauto.
  inv H0; constructor; eauto.
Qed.

Lemma agree_wk_re Γ :
  agree_wk [[re Γ]] [[Γ]].
Proof.
  induction Γ.
  - simpl; constructor.
  - destruct a. 
    destruct p.
    destruct s; simpl; constructor; eauto.
    constructor; eauto.
Qed.

Lemma agree_wk_merge_inv Γ1 Γ2 Γ :
  merge Γ1 Γ2 Γ ->
  agree_wk [[Γ1]] [[Γ]] /\
  agree_wk [[Γ2]] [[Γ]].
Proof with eauto using agree_wk.
  intro H.
  dependent induction H; simpl; firstorder...
Qed.

Lemma wk_ok Γ1 m A : 
  [ Γ1 |- m :- A ] ->
  forall Γ2, agree_wk Γ1 Γ2 ->
    [ Γ2 |- m :- A ].
Proof.
  intro H.
  dependent induction H; simpl; intros; subst.
  - apply p_axiom.
  - apply t_axiom.
  - eapply ty_prop; eauto.
    apply IHhas_type2; constructor; eauto.
  - apply ty_prod.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - pose proof (agree_wk_has H0 H).
    apply ty_var; eauto.
  - eapply ty_lam.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_app.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
  - eapply ty_conv.
    apply H.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
Qed.

Lemma erase_re Γ m A :
  [ [[re Γ]] |- m :- A ] ->
  [ [[Γ]] |- m :- A ].
Proof.
  intro H.
  eapply wk_ok; eauto.
  apply agree_wk_re.
Qed.

Lemma erase_subst_trivial n :
  erase_subst (n .: ids) ([|n|] .: ids).
Proof.
  unfold erase_subst; intros.
  destruct x; simpl; eauto.
Qed.

Theorem embedding Γ m A s : 
  [ Γ |- m :- A -: s ] ->
  [ [[ Γ ]] |- [| m |] :- [| A |] ].
Proof.
  intro H.
  dependent induction H; asimpl.
  - apply p_axiom.  
  - apply t_axiom.  
  - eapply ty_prop; eauto.
  - apply ty_prod; eauto.
  - apply ty_prod; eauto.
    simpl in IHhas_type2.
    eapply wk_ok; eauto.
    constructor.
    apply agree_wk_refl.
  - apply hasU_erase in H.
    apply ty_var; eauto.
  - apply hasL_erase in H.
    apply ty_var; eauto.
  - simpl in IHhas_type1.
    destruct s; simpl in IHhas_type2; eapply ty_lam; eauto.
  - simpl in IHhas_type1.
    destruct s; simpl in IHhas_type2. 
    + eapply ty_lam; eauto.
      apply erase_re; eauto.
    + eapply ty_lam; eauto.
      apply erase_re; eauto.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H2; destruct H2.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - simpl in IHhas_type1.
    apply agree_wk_merge_inv in H1; destruct H1.
    erewrite (erase_subst_com); eauto.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
    apply erase_subst_trivial.
  - eapply ty_conv.
    apply erase_sub; eauto.
    simpl in IHhas_type1.
    eapply wk_ok; eauto.
    apply agree_wk_re.
    apply IHhas_type2.
Qed.

Corollary embedding_context Γ :
  CLC.context_ok Γ -> [ [[Γ]] |- ].
Proof.
  induction 1; simpl. 
  constructor.
  apply embedding in H0.
  apply erase_re in H0.
  econstructor; eauto.
  apply embedding in H0.
  apply erase_re in H0.
  econstructor; eauto.
  constructor; eauto.
Qed.

End CLC.