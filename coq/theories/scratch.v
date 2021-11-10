From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CLC.

Declare Scope cilc_scope.
Open Scope cilc_scope.

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
  - simpl; constructor.
  - destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto.
Qed.

Lemma merge_re2 T (Gamma : context T) :
  merge Gamma (re Gamma) Gamma.
Proof.
  induction Gamma.
  - simpl; constructor.
  - destruct a.
    destruct p.
    destruct s; simpl.
    constructor; eauto.
    constructor; eauto.
    simpl.
    constructor; eauto.
Qed.

Lemma merge_pure_inv T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma -> 
  pure Gamma1 /\ pure Gamma2.
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

Lemma merge_pure1 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma1 -> 
  Gamma = Gamma2.
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

Lemma merge_pure2 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma2 -> 
  Gamma = Gamma1.
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

Lemma merge_pure_pure T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma1 ->
  pure Gamma2 ->
  pure Gamma.
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    constructor; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    constructor; eauto.
Qed.

Lemma merge_pure_eq T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  pure Gamma1 -> 
  pure Gamma2 -> 
  Gamma1 = Gamma2.
Proof.
  induction 1; intros; eauto.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
  - inv H0.
  - inv H1.
  - inv H0; inv H1.
    rewrite IHmerge; eauto.
Qed.

Lemma merge_re_re T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma -> 
  re Gamma1 = re Gamma /\ re Gamma2 = re Gamma.
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

Lemma merge_re_re_re T (Gamma : context T) : 
  merge (re Gamma) (re Gamma) (re Gamma).
Proof.
  induction Gamma; intros.
  constructor.
  destruct a.
  destruct p.
  destruct s.
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

Lemma re_re T (Gamma : context T) :
  re Gamma = re (re Gamma).
Proof.
  induction Gamma.
  - simpl.
    reflexivity.
  - case a; intros; simpl.
    case p; intros; simpl.
    case s; intros; simpl.
    rewrite <- IHGamma; eauto.
    rewrite <- IHGamma; eauto.
    rewrite <- IHGamma; eauto.
Qed.

Lemma pure_re T (Gamma : context T) :
  pure Gamma -> Gamma = re Gamma.
Proof.
  induction Gamma; intros.
  - eauto.
  - inv H; simpl.
    rewrite <- IHGamma; eauto.
    rewrite <- IHGamma; eauto.
Qed.

Lemma re_pure T (Gamma : context T) : pure (re Gamma).
Proof.
  induction Gamma; intros.
  constructor.
  destruct a; simpl. 
  destruct p; simpl. 
  destruct s; simpl. 
  constructor; eauto.
  constructor; eauto.
  constructor; eauto.
Qed.

Lemma hasU_re {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> hasU (re Gamma) x A.
Proof.
  induction 1; simpl.
  - constructor.
    rewrite <- pure_re; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma hasL_re {T} `{Ids T} `{Subst T} (Gamma : context T) :
  forall x A, ~hasL (re Gamma) x A.
Proof.
  induction Gamma; unfold not; intros.
  - simpl in H1. inv H1.
  - destruct a; inv H1. 
    destruct p; inv H2. 
    destruct s; inv H4. 
    destruct p; inv H2. 
    destruct s; inv H4. 
    eapply IHGamma; eauto.
    destruct p; inv H2. 
    destruct s; inv H4. 
    eapply IHGamma; eauto.
    eapply IHGamma; eauto.
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
  inv h.
  inv h; eauto.
  inv h; eauto.
Qed.

Lemma hasU_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> forall B, hasU Gamma x B -> A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasU in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasU in H5. rewrite H5; eauto.
Qed.

Lemma hasL_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasL Gamma x A -> forall B, hasL Gamma x B -> A = B.
Proof.
  induction 1; intros.
  inv H2; eauto.
  inv H2; eauto.
  apply IHhasL in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhasL in H5. rewrite H5; eauto.
Qed.

Lemma hasU_hasL {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  hasU Gamma x A -> forall B, ~hasL Gamma x B.
Proof.
  induction 1; unfold not; intros.
  inv H2.
  inv H2; apply IHhasU in H7; eauto.
  inv H2; apply IHhasU in H5; eauto.
Qed.

Lemma merge_split1 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Gamma1 ->
    exists Delta,
      merge Delta1 Gamma2 Delta /\ merge Delta Delta2 Gamma.
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
      exists (+n x).
      repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (m +l x).
    repeat constructor; eauto.
  - inv H0.
    specialize (IHmerge _ _ H4).
    firstorder.
    exists (+n x).
    repeat constructor; eauto.
Qed.

Lemma merge_split2 T (Gamma1 Gamma2 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma ->
  forall Delta1 Delta2,
    merge Delta1 Delta2 Gamma1 ->
    exists Delta,
      merge Delta2 Gamma2 Delta /\ merge Delta1 Delta Gamma.
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
      exists (+n x).
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
    exists (+n x).
    repeat constructor; eauto.
Qed.

Inductive term : Type :=
| Var    (x : var)
| Sort   (s : sort) (l : option nat)
| Prod   (A : term) (B : {bind term}) (s : sort)
| Lolli  (A : term) (B : {bind term}) (s : sort)
| Lam    (m : {bind term})
| App    (m n : term)
| Ind    (A : term) (s : sort) (Cs : list {bind term})
| Constr (i : nat) (m : term)
| Case   (m Q : term) (Fs : list term)
| DCase  (m Q : term) (Fs : list term)
| Fix    (m : {bind term}).

Section term_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x).
  Hypothesis ih_Sort : forall s l, P (Sort s l).
  Hypothesis ih_Prod : forall A B s, P A -> P B -> P (Prod A B s).
  Hypothesis ih_Lolli : forall A B s, P A -> P B -> P (Lolli A B s).
  Hypothesis ih_Lam : forall m, P m -> P (Lam m).
  Hypothesis ih_App : forall m n, P m -> P n -> P (App m n).
  Hypothesis ih_Ind : forall A s Cs, P A -> List.Forall P Cs -> P (Ind A s Cs).
  Hypothesis ih_Constr : forall i m, P m -> P (Constr i m).
  Hypothesis ih_Case : 
    forall m Q Fs, P m -> P Q -> List.Forall P Fs -> P (Case m Q Fs).
  Hypothesis ih_DCase : 
    forall m Q Fs, P m -> P Q -> List.Forall P Fs -> P (DCase m Q Fs).
  Hypothesis ih_Fix : forall m, P m -> P (Fix m).

  Fixpoint term_ind_nested m : P m.
  Proof.
    pose ih_nested := (
      fix fold xs : List.Forall P xs :=
        match xs with
        | nil => List.Forall_nil _
        | x :: xs => List.Forall_cons _ (term_ind_nested x) (fold xs)
        end).
    case m.
    apply ih_Var.
    apply ih_Sort.
    intros; apply ih_Prod.
      apply term_ind_nested.
      apply term_ind_nested.
    intros; apply ih_Lolli.
      apply term_ind_nested.
      apply term_ind_nested.
    intros; apply ih_Lam.
      apply term_ind_nested.
    intros; apply ih_App.
      apply term_ind_nested.
      apply term_ind_nested.
    intros; apply ih_Ind.
      apply term_ind_nested.
      apply ih_nested.
    intros; apply ih_Constr.
      apply term_ind_nested.
    intros; apply ih_Case.
      apply term_ind_nested.
      apply term_ind_nested.
      apply ih_nested.
    intros; apply ih_DCase.
      apply term_ind_nested.
      apply term_ind_nested.
      apply ih_nested.
    intros; apply ih_Fix.
      apply term_ind_nested.
  Qed.
End term_ind_nested.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Fixpoint spine (h : term) (ls : list term) : term :=
  match ls with
  | nil => h
  | m :: ls => spine (App h m) ls
  end.

Inductive iget : nat -> list term -> term -> Prop :=
| iget_O m ls :
  iget 0 (m :: ls) m
| iget_S n m m' ls :
  iget n ls m ->
  iget (S n) (m' :: ls) m.

Inductive One2 R : list term -> list term -> Prop :=
| One2_hd m m' ls :
  R m m' ->
  One2 R (m :: ls) (m' :: ls)
| One2_tl m ls ls' :
  One2 R ls ls' ->
  One2 R (m :: ls) (m :: ls').

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
| step_Beta m n :
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
  One2 step Cs Cs' ->
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
  One2 step Fs Fs' ->
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
  One2 step Fs Fs' ->
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
  step (Fix m) (m.[Fix m/]).

Section step_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_Lam : 
    forall m m', step m m' -> P m m' -> P (Lam m) (Lam m').
  Hypothesis ih_AppL : 
    forall m m' n, step m m' -> P m m' -> P (App m n) (App m' n).
  Hypothesis ih_AppR :
    forall m n n', step n n' -> P n n' -> P (App m n) (App m n').
  Hypothesis ih_Beta : 
    forall m n, P (App (Lam m) n) m.[n/].
  Hypothesis ih_ProdL :
    forall A A' B s, step A A' -> P A A' -> P (Prod A B s) (Prod A' B s).
  Hypothesis ih_ProdR :
    forall A B B' s, step B B' -> P B B' -> P (Prod A B s) (Prod A B' s).
  Hypothesis ih_LolliL :
    forall A A' B s, step A A' -> P A A' -> P (Lolli A B s) (Lolli A' B s).
  Hypothesis ih_LolliR :
    forall A B B' s, step B B' -> P B B' -> P (Lolli A B s) (Lolli A B' s).
  Hypothesis ih_IndA :
    forall A A' s Cs, step A A' -> P A A' -> P (Ind A s Cs) (Ind A' s Cs).
  Hypothesis ih_IndCs :
    forall A s Cs Cs', One2 step Cs Cs' -> One2 P Cs Cs' -> 
      P (Ind A s Cs) (Ind A s Cs').
  Hypothesis ih_Constr :
    forall i m m', step m m' -> P m m' -> P (Constr i m) (Constr i m').
  Hypothesis ih_CaseM :
    forall m m' Q Fs, step m m' -> P m m' -> P (Case m Q Fs) (Case m' Q Fs).
  Hypothesis ih_CaseQ :
    forall m Q Q' Fs, step Q Q' -> P Q Q' -> P (Case m Q Fs) (Case m Q' Fs).
  Hypothesis ih_CaseFs :
    forall m Q Fs Fs', One2 step Fs Fs' -> One2 P Fs Fs' -> 
      P (Case m Q Fs) (Case m Q Fs').
  Hypothesis ih_CaseIota : 
    forall i m ms Q Fs F, iget i Fs F ->
      P (Case (spine (Constr i m) ms) Q Fs) (spine F ms).
  Hypothesis ih_DCaseM :
    forall m m' Q Fs, step m m' -> P m m' -> P (DCase m Q Fs) (DCase m' Q Fs).
  Hypothesis ih_DCaseQ :
    forall m Q Q' Fs, step Q Q' -> P Q Q' -> P (DCase m Q Fs) (DCase m Q' Fs).
  Hypothesis ih_DCaseFs :
    forall m Q Fs Fs', One2 step Fs Fs' -> One2 P Fs Fs' -> 
      P (DCase m Q Fs) (DCase m Q Fs').
  Hypothesis ih_DCaseIota : 
    forall i m ms Q Fs F, iget i Fs F ->
      P (DCase (spine (Constr i m) ms) Q Fs) (spine F ms).
  Hypothesis ih_Fix :
    forall m m', step m m' -> P m m' -> P (Fix m) (Fix m').
  Hypothesis ih_FixIota :
    forall m, P (Fix m) (m.[Fix m/]).

  Fixpoint step_ind_nested m m' (st : step m m') : P m m'.
  Proof.
    pose ih_nested := (
      fix fold ls1 ls2 (p : One2 step ls1 ls2) : One2 P ls1 ls2 :=
        match p with
        | One2_hd _ _ _ hd => One2_hd _ (step_ind_nested _ _ hd)
        | One2_tl _ _ _ tl => One2_tl _ (fold _ _ tl)
        end).
    case st.
    intros; apply ih_Lam.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_AppL.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_AppR.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_Beta.
    intros; apply ih_ProdL.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_ProdR.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_LolliL.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_LolliR.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_IndA.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_IndCs.
      apply H.
      apply ih_nested; apply H.
    intros; apply ih_Constr.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_CaseM.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_CaseQ.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_CaseFs.
      apply H.
      apply ih_nested; apply H.
    intros; apply ih_CaseIota.
      apply H.
    intros; apply ih_DCaseM.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_DCaseQ.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_DCaseFs.
      apply H.
      apply ih_nested; apply H.
    intros; apply ih_DCaseIota.
      apply H.
    intros; apply ih_Fix.
      apply H.
      apply step_ind_nested; apply H.
    intros; apply ih_FixIota.
  Qed.
End step_ind_nested.

Inductive All2 R : list term -> list term -> Prop :=
| All2_nil : All2 R nil nil
| All2_cons m m' ls ls' :
  R m m' ->
  All2 R ls ls' ->
  All2 R (m :: ls) (m' :: ls').

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
| pstep_Beta m m' n n' :
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
  All2 pstep Cs Cs' ->
  pstep (Ind A s Cs) (Ind A' s Cs')
| pstep_Constr i m m' :
  pstep m m' ->
  pstep (Constr i m) (Constr i m')
| pstep_Case m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  All2 pstep Fs Fs' ->
  pstep (Case m Q Fs) (Case m' Q' Fs')
| pstep_CaseIota i m ms ms' Q Fs Fs' F' :
  iget i Fs' F' ->
  All2 pstep ms ms' ->
  All2 pstep Fs Fs' ->
  pstep 
    (Case (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_DCase m m' Q Q' Fs Fs' :
  pstep m m' ->
  pstep Q Q' ->
  All2 pstep Fs Fs' ->
  pstep (DCase m Q Fs) (DCase m' Q' Fs')
| pstep_DCaseIota i m ms ms' Q Fs Fs' F' :
  iget i Fs' F' ->
  All2 pstep ms ms' ->
  All2 pstep Fs Fs' ->
  pstep 
    (DCase (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_Fix m m' :
  pstep m m' ->
  pstep (Fix m) (Fix m')
| pstep_FixIota m m' :
  pstep m m' ->
  pstep (Fix m) (m'.[Fix m'/]).

Section pstep_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x) (Var x).
  Hypothesis ih_Sort : forall srt l, P (Sort srt l) (Sort srt l).
  Hypothesis ih_Lam : 
    forall n n', pstep n n' -> P n n' -> P (Lam n) (Lam n').
  Hypothesis ih_App :
    forall m m' n n', pstep m m' -> P m m' -> pstep n n' -> P n n' -> 
      P (App m n) (App m' n').
  Hypothesis ih_Beta :
    forall m m' n n', pstep m m' -> P m m' -> pstep n n' -> P n n' ->
      P (App (Lam m) n) m'.[n'/].
  Hypothesis ih_Prod :
    forall A A' s B B', pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Prod A B s) (Prod A' B' s).
  Hypothesis ih_Lolli :
    forall A A' s B B', pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Lolli A B s) (Lolli A' B' s).
  Hypothesis ih_Ind :
    forall A A' s Cs Cs', 
      pstep A A' -> P A A' -> 
      All2 pstep Cs Cs' -> All2 P Cs Cs' ->
      P (Ind A s Cs) (Ind A' s Cs').
  Hypothesis ih_Constr :
    forall i m m', pstep m m' -> P m m' -> P (Constr i m) (Constr i m').
  Hypothesis ih_Case :
    forall m m' Q Q' Fs Fs', 
      pstep m m' -> P m m' -> 
      pstep Q Q' -> P Q Q' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (Case m Q Fs) (Case m' Q' Fs').
  Hypothesis ih_CaseIota :
    forall i m ms ms' Q Fs Fs' F',
      iget i Fs' F' ->
      All2 pstep ms ms' -> All2 P ms ms' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (Case (spine (Constr i m) ms) Q Fs) (spine F' ms').
  Hypothesis ih_DCase :
    forall m m' Q Q' Fs Fs', 
      pstep m m' -> P m m' -> 
      pstep Q Q' -> P Q Q' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (DCase m Q Fs) (DCase m' Q' Fs').
  Hypothesis ih_DCaseIota :
    forall i m ms ms' Q Fs Fs' F',
      iget i Fs' F' ->
      All2 pstep ms ms' -> All2 P ms ms' ->
      All2 pstep Fs Fs' -> All2 P Fs Fs' ->
      P (DCase (spine (Constr i m) ms) Q Fs) (spine F' ms').
  Hypothesis ih_Fix :
    forall m m', pstep m m' -> P m m' -> P (Fix m) (Fix m').
  Hypothesis ih_FixIota :
    forall m m', pstep m m' -> P m m' -> P (Fix m) (m'.[Fix m'/]).
  
  Fixpoint pstep_ind_nested m m' (st : pstep m m') : P m m'.
  Proof.
    pose ih_nested := (
      fix fold ls1 ls2 (p : All2 pstep ls1 ls2) : All2 P ls1 ls2 :=
        match p with
        | All2_nil => All2_nil _
        | All2_cons _ _ _ _ hd tl =>
          All2_cons (pstep_ind_nested _ _ hd) (fold _ _ tl)
        end).
    case st.
    apply ih_Var.
    apply ih_Sort.
    intros; apply ih_Lam.
      apply H.
      apply pstep_ind_nested; apply H.
    intros; apply ih_App.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply pstep_ind_nested; apply H0.
    intros; apply ih_Beta.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply pstep_ind_nested; apply H0.
    intros; apply ih_Prod.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply pstep_ind_nested; apply H0.
    intros; apply ih_Lolli.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply pstep_ind_nested; apply H0.
    intros; apply ih_Ind.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply ih_nested; apply H0.
    intros; apply ih_Constr.
      apply H.
      apply pstep_ind_nested; apply H.
    intros; apply ih_Case.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply pstep_ind_nested; apply H0.
      apply H1.
      apply ih_nested; apply H1.
    intros; eapply ih_CaseIota.
      apply H.
      apply H0.
      apply ih_nested; apply H0.
      apply H1.
      apply ih_nested; apply H1.
    intros; apply ih_DCase.
      apply H.
      apply pstep_ind_nested; apply H.
      apply H0.
      apply pstep_ind_nested; apply H0.
      apply H1.
      apply ih_nested; apply H1.
    intros; eapply ih_DCaseIota.
      apply H.
      apply H0.
      apply ih_nested; apply H0.
      apply H1.
      apply ih_nested; apply H1.
    intros; apply ih_Fix.
      apply H.
      apply pstep_ind_nested; apply H.
    intros; apply ih_FixIota.
      apply H.
      apply pstep_ind_nested; apply H.
  Qed.
End pstep_ind_nested.

Notation red := (star step).
Notation "m ~~ n" := (conv step m n) (at level 30).

Definition sred sigma tau := 
  forall x : var, red (sigma x) (tau x).

Fixpoint spine' (h : term) (ls : list term) : term :=
  match ls with
  | nil => h
  | m :: ls => App (spine' h ls) m
  end.

Lemma One2_map R Q ls1 ls2 :
  (forall m n, R m n -> R (Q m) (Q n)) -> 
    One2 R ls1 ls2 -> One2 R (map Q ls1) (map Q ls2).
Proof.
  move=> f One2.
  elim: One2 f.
  move=> m m' ls r f.
    constructor.
    exact: f.
  move=> m ls ls' One2 ih f //=.
    constructor.
    exact: ih.
Qed.

Lemma rev_inj (ls1 ls2 : list term) : rev ls1 = rev ls2 -> ls1 = ls2.
Proof.
  move=> e.
  move:e=> /(f_equal rev).
  by rewrite! revK.
Qed.

Lemma spine_append h xs ys :
  spine h (xs ++ ys) = spine (spine h xs) ys.
Proof. elim: xs ys h=> //=. Qed.

Lemma spine_rev h m ls :
  App (spine h (rev ls)) m = spine h (rev (m :: ls)).
Proof.
  elim: ls h m=> //=.
  move=> t ls ih h m.
  rewrite <-cat1s.
  rewrite rev_cat.
  rewrite spine_append=> //=.
  rewrite <-cat1s.
  rewrite rev_cat.
  rewrite spine_append=> //=.
  by rewrite <- ih.
Qed.

Lemma spine_rev_spine' h ls :
  spine h (rev ls) = spine' h ls.
Proof.
  elim: ls h=> //=.
  move=> t t0 ih h.
  rewrite <- ih.
  by rewrite spine_rev.
Qed.

Lemma spine_spine'_rev h ls :
  spine h ls = spine' h (rev ls).
Proof.
  have pf := spine_rev_spine' h (rev ls).
  by rewrite revK in pf.
Qed.

Lemma spine'_Constr i1 i2 h1 h2 ls1 ls2 :
  spine' (Constr i1 h1) ls1 = spine' (Constr i2 h2) ls2 ->
    i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  elim: ls1 ls2 i1 i2 h1 h2=>//=.
  move=> ls2 i1 i2 h1 h2.
    destruct ls2=> //= e. by inv e.
  move=> t ls1 ih ls2 t1 t2 h1 h2.
    destruct ls2=> //= e.
    inv e.
    by move: H0=> /ih [->[->->]].
Qed.

Lemma spine_Constr i1 i2 h1 h2 ls1 ls2 :
  spine (Constr i1 h1) ls1 = spine (Constr i2 h2) ls2 ->
    i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  rewrite! spine_spine'_rev=> /spine'_Constr[->[->e]].
  by move: e=> /rev_inj->.
Qed.

Lemma spine_subst sigma h ls :
  (spine h ls).[sigma] = spine (h.[sigma]) ls..[sigma].
Proof.
  move: sigma h. elim: ls => //.
  move=> a l ih sigma h.
    replace ((a :: l)..[sigma]) 
      with (a.[sigma] :: l..[sigma])
      by autosubst; simpl.
    replace (App h.[sigma] a.[sigma]) with (App h a).[sigma]
      by autosubst.
    apply ih.
Qed.

Lemma iget_iget ls i m1 m2 :
  iget i ls m1 -> iget i ls m2 -> m1 = m2.
Proof.
  move=> ig. elim: ig m2.
  move=> m ls0 m2 ig. by inv ig.
  move=> n m m' ls0 ig1 ih m2 ig2. inv ig2.
    by move: H3=> /ih.
Qed.

Lemma iget_subst sigma i ls m :
  iget i ls m -> iget i ls..[sigma] m.[sigma].
Proof.
  move=> ig. elim: ig; asimpl.
  move=> m0 ls0; by constructor.
  move=> n m0 m' ls0 ig ih; by constructor.
Qed.

Lemma step_subst sigma m n (st : step m n) : 
  step m.[sigma] n.[sigma].
Proof with eauto using step.
  move: m n st sigma.
  apply: step_ind_nested; asimpl... 
  move=> m n sigma.
    replace (m.[n/].[sigma]) with (m.[up sigma].[n.[sigma]/])
    by autosubst.
    exact: step_Beta.
  move=> A s Cs Cs' h ih sigma; asimpl. 
    constructor.
    elim: ih=> //=.
    intros; constructor; asimpl...
    intros; constructor; asimpl...
  move=> m Q Fs Fs' h ih sigma; asimpl.
    constructor.
    elim: ih=> //=.
    intros; constructor; asimpl...
    intros; constructor; asimpl...
  move=> i m ms Q Fs F ig sigma.
    repeat (rewrite spine_subst; asimpl).
    constructor.
    exact: iget_subst.
  move=> m Q Fs Fs' h ih sigma; asimpl.
    constructor.
    elim: ih=> //=.
    intros; constructor; asimpl...
    intros; constructor; asimpl...
  move=> i m ms Q Fs F ig sigma; asimpl.
    repeat (rewrite spine_subst; asimpl).
    constructor.
    exact: iget_subst.
  move=> m sigma.
    replace m.[Fix m/].[sigma] with m.[up sigma].[Fix m.[up sigma]/]
      by autosubst.
    constructor.
Qed.

Lemma red_App m1 m2 n1 n2 :
  red m1 m2 -> red n1 n2 -> red (App m1 n1) (App m2 n2).
Proof.
  move=> A B. apply: (star_trans (App m2 n1)).
  apply: (star_hom (App^~ n1)) A=> x y. exact: step_AppL.
  apply: star_hom B=> x y. exact: step_AppR.
Qed.

Lemma red_Lam s1 s2 : red s1 s2 -> red (Lam s1) (Lam s2).
Proof. apply: star_hom=> x y. exact: step_Lam. Qed.

Lemma red_Prod A1 A2 B1 B2 s :
  red A1 A2 -> red B1 B2 -> red (Prod A1 B1 s) (Prod A2 B2 s).
Proof.
  move=> A B. apply: (star_trans (Prod A2 B1 s)).
  apply: (star_hom ((Prod^~ B1)^~ s)) A=> x y. exact: step_ProdL.
  apply: (star_hom ((Prod A2)^~ s)) B => x y. exact: step_ProdR.
Qed.

Lemma red_Lolli A1 A2 B1 B2 s :
  red A1 A2 -> red B1 B2 -> red (Lolli A1 B1 s) (Lolli A2 B2 s).
Proof.
  move=> A B. apply: (star_trans (Lolli A2 B1 s)).
  apply: (star_hom ((Lolli^~ B1)^~ s)) A=> x y. exact: step_LolliL.
  apply: (star_hom ((Lolli A2)^~ s)) B=> x y. exact: step_LolliR.
Qed.

Lemma red_Ind A1 A2 s Cs1 Cs2 :
  red A1 A2 -> star (One2 step) Cs1 Cs2 -> 
    red (Ind A1 s Cs1) (Ind A2 s Cs2).
Proof.
  move=> A B. 
  apply: (star_trans (Ind A2 s Cs1)).
  apply: (star_hom ((Ind^~ s)^~ Cs1)) A=> x y. exact: step_IndA.
  elim: B=> //.
    move=> y z rd' rd st.
    apply: star_trans.
      by apply: rd.
      by apply: star1; eauto using step.
Qed.

Lemma red_Constr i m1 m2 :
  red m1 m2 -> red (Constr i m1) (Constr i m2).
Proof.
  move=> A.
  apply: (star_hom (Constr i)) A => x y. exact: step_Constr.
Qed.

Lemma red_Case m1 m2 Q1 Q2 Fs1 Fs2 :
  red m1 m2 -> red Q1 Q2 -> star (One2 step) Fs1 Fs2 -> 
    red (Case m1 Q1 Fs1) (Case m2 Q2 Fs2).
Proof.
  move=> A B C. 
  apply: (star_trans (Case m2 Q1 Fs1)).
  apply: (star_hom ((Case^~ Q1)^~ Fs1)) A=> x y. exact: step_CaseM.
  apply: (star_trans (Case m2 Q2 Fs1)).
  apply: (star_hom ((Case m2)^~ Fs1)) B=> x y. exact: step_CaseQ.
  elim: C=> //.
    move=> y z rd' rd st.
    apply: star_trans.
      by apply: rd.
      by apply: star1; eauto using step.
Qed.

Lemma red_DCase m1 m2 Q1 Q2 Fs1 Fs2 :
  red m1 m2 -> red Q1 Q2 -> star (One2 step) Fs1 Fs2 -> 
    red (DCase m1 Q1 Fs1) (DCase m2 Q2 Fs2).
Proof.
  move=> A B C. 
  apply: (star_trans (DCase m2 Q1 Fs1)).
  apply: (star_hom ((DCase^~ Q1)^~ Fs1)) A=> x y. exact: step_DCaseM.
  apply: (star_trans (DCase m2 Q2 Fs1)).
  apply: (star_hom ((DCase m2)^~ Fs1)) B=> x y. exact: step_DCaseQ.
  elim: C=> //.
    move=> y z rd' rd st.
    apply: star_trans.
      by apply: rd.
      by apply: star1; eauto using step.
Qed.

Lemma red_Fix m1 m2 :
  red m1 m2 -> red (Fix m1) (Fix m2).
Proof.
  move=> A.
  apply: (star_hom Fix) A=> x y. exact: step_Fix.
Qed.

Lemma red_hd h1 h2 ls :
  red h1 h2 -> star (One2 step) (h1 :: ls) (h2 :: ls).
Proof.
  move=> rd. elim: rd ls=> //.
  move=> y z rd ih st ls.
  apply: star_trans.
    by apply: ih.
    by apply: star1; constructor.
Qed.

Lemma red_tl h ls ls' :
  star (One2 step) ls ls' -> star (One2 step) (h :: ls) (h :: ls').
Proof.
  move=> rd. elim: rd h=> //.
  move=> y z rd ih st h.
  apply: star_trans.
    by apply: ih.
    by apply: star1; constructor.
Qed.

Lemma red_ls h h' ls ls' :
  red h h' ->
  star (One2 step) ls ls' -> 
  star (One2 step) (h :: ls) (h' :: ls').
Proof.
  move=> hd tl.
  apply: star_trans.
    apply: red_hd.
    apply: hd.
    exact: red_tl.
Qed.

Lemma red_nil_inv ls : star (One2 step) nil ls -> ls = nil.
Proof. 
  elim=> //.
  move=> y z _ -> st. by inv st.
Qed.

Lemma red_cons_inv m ls l : 
  star (One2 step) (m :: ls) l -> 
  exists m' ls', 
    l = m' :: ls' /\ red m m' /\ star (One2 step) ls ls'.
Proof.
  elim=> //.
  by exists m; exists ls=> //.
  move=> y z rd [m0 [ls0 [-> [rd1 rd2]]]] st. inv st.
    exists m'; exists ls0; split=> //.
      split. apply: starSE. exact: rd1. exact: H2. exact: rd2.
    exists m0; exists ls'; split=> //.
      split. exact: rd1. apply: starSE. exact: rd2. exact: H2.
Qed.

Lemma red_spine h h' ls ls' :
  red h h' -> star (One2 step) ls ls' -> 
    red (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=> ls' h h' rd /red_nil_inv -> //.
  move=> t t0 ih ls' h h' rd rd'=> //=.
  apply: (star_trans (spine (App h' t) t0)).  
    apply: ih=> //.
    exact: red_App.
  move: rd'=> /red_cons_inv [m [ls [-> [rd1 rd2]]]] //=.
    apply: ih.
    exact: red_App.
    exact: rd2.
Qed.

Lemma red_subst sigma m n :
  red m n -> red m.[sigma] n.[sigma].
Proof.
  move=> rd. elim: rd sigma=> /={n}.
  move=> sigma //.
  move=> y z rd ih st sigma.
    have rd1 := ih sigma.
    apply: star_trans.
    apply: rd1.
    move: st=> /(step_subst sigma) rd2.
    by apply: star1.
Qed.

Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. 
  move=> A [|n] //=; asimpl. 
  apply: red_subst. 
  exact: A. 
Qed.

Hint Resolve 
  red_App red_Lam red_Prod red_Lolli 
  red_Ind red_Constr red_Case red_DCase red_Fix
  red_ls red_subst sred_up 
: red_congr.

Lemma red_compat sigma tau s : 
  sred sigma tau -> red s.[sigma] s.[tau].
Proof.
  move: s sigma tau.
  apply: term_ind_nested; asimpl; eauto 6 with red_congr.
  move=> A s Cs ih h sigma tau sr.
    apply: red_Ind; eauto.
    elim: h=> //=; eauto 6 with red_congr.
  move=> m Q Fs ih1 ih2 ih3 sigma tau sr.
    apply: red_Case; eauto.
    elim: ih3=> //=; eauto 6 with red_congr.
  move=> m Q Fs ih1 ih2 ih3 sigma tau sr.
    apply: red_DCase; eauto.
    elim: ih3=> //=; eauto 6 with red_congr.
Qed.

Definition sconv (sigma tau : var -> term) := 
  forall x, sigma x ~~ tau x.

Lemma conv_Lam m1 m2 : m1 ~~ m2 -> Lam m1 ~~ Lam m2.
Proof. apply: conv_hom=> x y. exact: step_Lam. Qed.

Lemma conv_Prod A1 A2 s B1 B2 :
  A1 ~~ A2 -> B1 ~~ B2 -> Prod A1 B1 s ~~ Prod A2 B2 s.
Proof.
  move=> A B.
  apply: (conv_trans (Prod A2 B1 s)).
  apply: (conv_hom ((Prod^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Prod A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_Lolli A1 A2 s B1 B2 :
  A1 ~~ A2 -> B1 ~~ B2 -> Lolli A1 B1 s ~~ Lolli A2 B2 s.
Proof.
  move=> A B.
  apply: (conv_trans (Lolli A2 B1 s)).
  apply: (conv_hom ((Lolli^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Lolli A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_App m1 m2 n1 n2 :
  m1 ~~ m2 -> n1 ~~ n2 -> App m1 n1 ~~ App m2 n2.
Proof.
  move=> A B.
  apply: (conv_trans (App m2 n1)).
  apply: (conv_hom (App^~ n1)) A=> x y ps.
    by constructor.
  apply: conv_hom B=> x y ps.
    by constructor.
Qed.

Lemma conv_Ind A1 A2 s Cs1 Cs2 :
  A1 ~~ A2 -> conv (One2 step) Cs1 Cs2 -> Ind A1 s Cs1 ~~ Ind A2 s Cs2.
Proof.
  move=> A B. 
  apply: (conv_trans (Ind A2 s Cs1)).
  apply: (conv_hom ((Ind^~ s)^~ Cs1)) A=> x y. exact: step_IndA.
  elim: B=> //.
    move=> y z cv' cv st.
    apply: (conv_trans (Ind A2 s y)).
      by apply: cv.
      by apply: conv1; eauto using step.
    move=> y z cv' cv st.
    apply: (conv_trans (Ind A2 s y)).
      by apply: cv.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_Constr i m1 m2 :
  m1 ~~ m2 -> Constr i m1 ~~ Constr i m2.
Proof.
  move=> A.
  apply: (conv_hom (Constr i)) A => x y. exact: step_Constr.
Qed.

Lemma conv_Case m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 ~~ m2 -> 
  Q1 ~~ Q2 -> 
  conv (One2 step) Fs1 Fs2 -> 
  Case m1 Q1 Fs1 ~~ Case m2 Q2 Fs2.
Proof.
  move=> A B C. 
  apply: (conv_trans (Case m2 Q1 Fs1)).
  apply: (conv_hom ((Case^~ Q1)^~ Fs1)) A=> x y. exact: step_CaseM.
  apply: (conv_trans (Case m2 Q2 Fs1)).
  apply: (conv_hom ((Case m2)^~ Fs1)) B=> x y. exact: step_CaseQ.
  elim: C=> //.
    move=> y z cv' cv st.
    apply: conv_trans.
      by apply: cv.
      by apply: conv1; eauto using step.
    move=> y z cv' cv st.
    apply: conv_trans.
      by apply: cv.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_DCase m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 ~~ m2 -> 
  Q1 ~~ Q2 -> 
  conv (One2 step) Fs1 Fs2 -> 
  DCase m1 Q1 Fs1 ~~ DCase m2 Q2 Fs2.
Proof.
  move=> A B C. 
  apply: (conv_trans (DCase m2 Q1 Fs1)).
  apply: (conv_hom ((DCase^~ Q1)^~ Fs1)) A=> x y. exact: step_DCaseM.
  apply: (conv_trans (DCase m2 Q2 Fs1)).
  apply: (conv_hom ((DCase m2)^~ Fs1)) B=> x y. exact: step_DCaseQ.
  elim: C=> //.
    move=> y z rd' rd st.
    apply: conv_trans.
      by apply: rd.
      by apply: conv1; eauto using step.
    move=> y z rd' rd st.
    apply: conv_trans.
      by apply: rd.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_Fix m1 m2 :
  m1 ~~ m2 -> Fix m1 ~~ Fix m2.
Proof.
  move=> A.
  apply: (conv_hom Fix) A=> x y. exact: step_Fix.
Qed.

Lemma conv_hd h1 h2 ls :
  h1 ~~ h2 -> conv (One2 step) (h1 :: ls) (h2 :: ls).
Proof.
  move=> cv. elim: cv ls=> //.
  move=> y z cv ih st ls.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1; constructor.
  move=> y z rd ih st ls.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1i; constructor.
Qed.

Lemma conv_tl h ls ls' :
  conv (One2 step) ls ls' -> conv (One2 step) (h :: ls) (h :: ls').
Proof.
  move=> cv. elim: cv h=> //.
  move=> y z cv ih st h.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1; constructor.
  move=> y z cv ih st h.
    apply: conv_trans.
      by apply: ih.
      by apply: conv1i; constructor.
Qed.

Lemma conv_ls h h' ls ls' :
  h ~~ h' ->
  conv (One2 step) ls ls' -> 
  conv (One2 step) (h :: ls) (h' :: ls').
Proof.
  move=> hd tl.
  apply: conv_trans.
    apply: conv_hd.
    apply: hd.
    exact: conv_tl.
Qed.

Lemma conv_subst sigma m n :
  m ~~ n -> m.[sigma] ~~ n.[sigma].
Proof.
  move=> cv. elim: cv sigma=> /={n}.
  move=> sigma //.
  move=> y z rd ih st sigma.
    have cv1 := ih sigma.
    apply: conv_trans.
    apply: cv1.
    move: st=> /(step_subst sigma) rd2.
    by apply: conv1.
  move=> y z rd ih st sigma.
    have cv1 := ih sigma.
    apply: conv_trans.
    apply: cv1.
    move: st=> /(step_subst sigma) rd2.
    by apply: conv1i.
Qed.

Lemma sconv_up sigma tau : 
  sconv sigma tau -> sconv (up sigma) (up tau).
Proof. 
  move=> A [|n] //=; asimpl. 
  apply: conv_subst. 
  exact: A. 
Qed.

Hint Resolve 
  conv_App conv_Lam conv_Prod conv_Lolli 
  conv_Ind conv_Constr conv_Case conv_DCase conv_Fix
  conv_ls conv_subst sconv_up 
: conv_congr.

Lemma conv_compat sigma tau s : 
  sconv sigma tau -> s.[sigma] ~~ s.[tau].
Proof.
  move: s sigma tau.
  apply: term_ind_nested; asimpl; eauto 6 with conv_congr. 
  move=> A s Cs ih h sigma tau sr.
    apply: conv_Ind; eauto.
    elim: h=> //=; eauto 6 with conv_congr.
  move=> m Q Fs ih1 ih2 ih3 sigma tau sr.
    apply: conv_Case; eauto.
    elim: ih3=> //=; eauto 6 with conv_congr.
  move=> m Q Fs ih1 ih2 ih3 sigma tau sr.
    apply: conv_DCase; eauto.
    elim: ih3=> //=; eauto 6 with conv_congr.
Qed.

Lemma conv_Beta s t1 t2 : t1 ~~ t2 -> s.[t1/] ~~ s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof.
  move: s.
  apply: term_ind_nested; eauto using pstep. 
  move=> A s Cs pA ih.
    constructor; eauto.
    elim: ih; eauto using pstep, All2.
  move=> m Q Fs pm pQ ih.
    constructor; eauto.
    elim: ih; eauto using pstep, All2.
  move=> m Q Fs pm pQ ih.
    constructor; eauto.
    elim: ih; eauto using pstep, All2.
Qed.

Lemma All2_pstep_refl ls : All2 pstep ls ls.
Proof with eauto using pstep_refl, All2. elim: ls... Qed.

Lemma step_pstep m m' : step m m' -> pstep m m'.
Proof with eauto using pstep, pstep_refl, All2, All2_pstep_refl.
  move: m m'.
  apply: step_ind_nested...
  intros; constructor...
    elim: H0...
  intros; constructor...
    elim: H0...
  intros; constructor...
    elim: H0...
Qed.

Lemma pstep_red m m' : pstep m m' -> red m m'.
Proof.
  move: m m'.
  apply: pstep_ind_nested=> //=; eauto with red_congr.
  move=> m m' n n' p1 r1 p2 r2.
    apply: starES.
    by econstructor.
    apply: (star_trans (m'.[n.:Var])). exact: red_subst.
    by apply: red_compat => -[|].
  move=> A A' s Cs Cs' pA rA pCs rCs.
    apply: red_Ind; eauto.
    elim: rCs; eauto with red_congr.
  move=> m m' Q Q' Fs Fs' pM rM pQ rQ pFs rFs.
    apply: red_Case; eauto.
    elim: rFs; eauto with red_congr.
  move=> i m ms ms' Q Fs Fs' F' ig pMs rMs pFs rFs.
    have ihMs : star (One2 step) ms ms'.
      elim: rMs; eauto with red_congr.
    have ihFs : star (One2 step) Fs Fs'.
      elim: rFs; eauto with red_congr.
    apply: star_trans.
    apply: red_Case.
    apply: red_spine.
    exact: starR.
    exact: ihMs.
    exact: starR.
    exact: ihFs.
    apply: star1.
    by constructor.
  move=> m m' Q Q' Fs Fs' pM rM pQ rQ pFs rFs.
    apply: red_DCase; eauto.
    elim: rFs; eauto with red_congr.
  move=> i m ms ms' Q Fs Fs' F' ig pMs rMs pFs rFs.
    have ihMs : star (One2 step) ms ms'.
      elim: rMs; eauto with red_congr.
    have ihFs : star (One2 step) Fs Fs'.
      elim: rFs; eauto with red_congr.
    apply: star_trans.
    apply: red_DCase.
    apply: red_spine.
    exact: starR.
    exact: ihMs.
    exact: starR.
    exact: ihFs.
    apply: star1.
    by constructor.
  move=> m m' p r.
    apply: star_trans.
    apply: red_Fix.
    exact: r.
    apply: star1.
    by constructor.
Qed.

Lemma pstep_subst sigma m m' :
  pstep m m' -> pstep m.[sigma] m'.[sigma].
Proof with eauto using pstep, pstep_refl, All2, All2_pstep_refl.
  move=> p. move: m m' p sigma.
  apply: pstep_ind_nested...
  move=> m m' n n' p1 ih1 p2 ih2 sigma; asimpl.
    have h1 := (ih1 (up sigma))=> {ih1}.
    have h2 := (ih2 sigma)=> {ih2}.
    have h3 := pstep_Beta (h1 Ids_term Rename_term) h2.
    by asimpl in h3.
  move=> A A' s Cs Cs' pA ihA pCs ihCs sigma; asimpl.
    constructor; eauto.
    elim: ihCs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs sigma; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs sigma; asimpl.
    rewrite! spine_subst.
    apply: pstep_CaseIota; eauto.
    apply: iget_subst. exact ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs sigma; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs sigma; asimpl.
    rewrite! spine_subst.
    apply: pstep_DCaseIota; eauto.
    apply: iget_subst. exact ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> m m' p ih sigma; asimpl.
    replace m'.[Fix m'.[up sigma] .: sigma]
      with (m'.[up sigma]).[Fix m'.[up sigma]/]
      by autosubst.
    exact: pstep_FixIota.
Qed.

Definition psstep (sigma tau : var -> term) := 
  forall x, pstep (sigma x) (tau x).

Lemma psstep_refl sigma : psstep sigma sigma.
Proof with eauto using pstep_refl.
  unfold psstep.
  induction x...
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau m m' :
  pstep m m' -> psstep sigma tau -> pstep m.[sigma] m'.[tau].
Proof with eauto 6 using pstep, All2, psstep_up.
  move=> p. move: m m' p sigma tau.
  apply: pstep_ind_nested... 
  move=> m m' n n' pM ihM pN ihN sigma tau pss; asimpl.
    have pss' := psstep_up pss.
    have hM := ihM _ _ pss'.
    have hN := ihN _ _ pss.
    have hBeta := pstep_Beta hM hN.
    by asimpl in hBeta.
  move=> A A' s Cs Cs' pA ihA pCs ihCs sigma tau pss; asimpl.
    constructor; eauto.
    elim: ihCs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs sigma tau pss; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs sigma tau pss; asimpl.
    rewrite! spine_subst.
    apply: pstep_CaseIota.
    apply: iget_subst. exact: ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs sigma tau pss; asimpl.
    constructor; eauto.
    elim: ihFs; asimpl...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs sigma tau pss; asimpl.
    rewrite! spine_subst.
    apply: pstep_DCaseIota.
    apply: iget_subst. exact: ig.
    elim: ihMs; asimpl...
    elim: ihFs; asimpl...
  move=> m m' p ih sigma tau ps; asimpl.
    replace m'.[Fix m'.[up tau] .: tau]
      with (m'.[up tau]).[Fix m'.[up tau]/]
      by autosubst.
    constructor.
    apply: ih.
    exact: psstep_up.
Qed.

Lemma psstep_compat sigma tau m1 m2 :
  psstep sigma tau -> pstep m1 m2 -> psstep (m1 .: sigma) (m2 .: tau).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep, All2, pstep_refl.
  move=> p.
  apply: pstep_compat...
  apply: psstep_compat...
  exact: psstep_refl.
Qed.

Lemma pstep_compat_Beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using psstep_refl, psstep_compat.
  move=> p1 p2.
  apply: pstep_compat...
Qed.

Lemma pstep_iget1 ls ls' i m :
  All2 pstep ls ls' -> iget i ls m -> exists m', iget i ls' m' /\ pstep m m'.
Proof with eauto using iget.
  move=> p.
  elim: p m i => {ls ls'}.
  move=> m i ig. inv ig.
  move=> m m' ls ls' p1 p2 ih m0 i ig. inv ig.
    exists m'...
    move: H3=> /ih [m'0 [ig p]].
    exists m'0...
Qed.

Lemma pstep_iget2 ls ls' i m' :
  All2 pstep ls ls' -> iget i ls' m' -> exists m, iget i ls m /\ pstep m m'.
Proof with eauto using iget.
  move=> p.
  elim: p m' i => {ls ls'}.
  move=> m' i ig. inv ig.
  move=> m m' ls ls' p1 p2 ih m0 i ig. inv ig.
    exists m...
    move: H3=> /ih[m1 [ig p]].
    exists m1...
Qed.

Lemma pstep_spine h h' ls ls' :
  pstep h h' -> All2 pstep ls ls' -> pstep (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=> ls' h h' p1 p2. inv p2=> //=.
  move=> t t0 ih ls h h' p p'. inv p'=> //=.
  apply: ih=> //.
  exact: pstep_App.
Qed.

Lemma spine_Lam_Constr_False m i h ls :
  ~Lam m = spine' (Constr i h) ls.
Proof. elim: ls=> //=. Qed.

Lemma pstep_spine'_inv i h ls m :
  pstep (spine' (Constr i h) ls) m -> 
    exists h' ls', 
      m = spine' (Constr i h') ls' /\ 
      pstep h h' /\ 
      All2 pstep ls ls'.
Proof with eauto using pstep, All2, pstep_refl, All2_pstep_refl.
  elim: ls h m.
  move=> h m //= p. inv p.
    exists m'. exists nil...
  move=> t t0 ih h m //= p. inv p.
    move: H1=>/ih[h'[ls'[->[p1 p2]]]].
    exists h'. exists (n' :: ls')...
    exfalso.
    by apply: spine_Lam_Constr_False; eauto.
Qed.

Lemma pstep_spine'_congr i h1 h2 ms1 ms2 :
  pstep (spine' (Constr i h1) ms1) (spine' (Constr i h2) ms2) ->
    All2 pstep ms1 ms2.
Proof with eauto using All2.
  elim: ms1 ms2 h2 =>//=.
  destruct ms2=> //=...
    move=> h2 p. by inv p.
  move=> h ls ih ms2 h2.
    destruct ms2=> //= p. 
    inv p. exfalso. by apply: spine_Lam_Constr_False; eauto.
    inv p. 
      move: H2=>/ih tl...
      exfalso. by apply: spine_Lam_Constr_False; eauto.
Qed.

Lemma pstep_append ls1 ls2 ls1' ls2' :
  All2 pstep ls1 ls2 -> All2 pstep ls1' ls2' ->
    All2 pstep (ls1 ++ ls1') (ls2 ++ ls2').
Proof with eauto using All2.
  move=> p. elim: p ls1' ls2'=> //={ls1 ls2}...
Qed.

Lemma pstep_rev ls1 ls2 :
  All2 pstep ls1 ls2 -> All2 pstep (rev ls1) (rev ls2).
Proof with eauto using All2.
  elim=> //={ls1 ls2}...
  move=> m m' ls ls' p1 p2 p3.
    replace (m :: ls) with ([:: m] ++ ls) by eauto.
    replace (m' :: ls') with ([:: m'] ++ ls') by eauto.
    rewrite! rev_cat.
    apply pstep_append...
Qed.

Lemma pstep_spine_inv i h ls m :
  pstep (spine (Constr i h) ls) m -> 
    exists h' ls', 
      m = spine (Constr i h') ls' /\ 
      pstep h h' /\ 
      All2 pstep ls ls'.
Proof with eauto using pstep, All2, pstep_refl, All2_pstep_refl.
  move=> p.
  move: (revK ls)=> e.
  rewrite <- e in p.
  rewrite spine_spine'_rev in p.
  move: p=> /pstep_spine'_inv[h'[ls'[->[p1 p2]]]].
  exists h'. exists (rev ls').
  rewrite spine_spine'_rev.
  rewrite revK.
  rewrite revK in p2.
  firstorder.
  apply pstep_rev in p2.
  by rewrite revK in p2.
Qed.

Lemma pstep_spine_congr i h1 h2 ms1 ms2 :
  pstep (spine (Constr i h1) ms1) (spine (Constr i h2) ms2) ->
    All2 pstep ms1 ms2.
Proof with eauto using pstep, All2, pstep_refl, All2_pstep_refl.
  move=> p.
  move: (revK ms1)=> e1.
  move: (revK ms2)=> e2.
  rewrite <- e1 in p=>{e1}.
  rewrite <- e2 in p=>{e2}.
  rewrite! spine_spine'_rev in p.
  move: p=> /pstep_spine'_congr.
  rewrite! revK=> /pstep_rev.
  by rewrite! revK.
Qed.

Lemma All2_diamond ls ls1 ls2 :
  All2 pstep ls ls1 ->
  All2 pstep ls ls2 ->
  All2 
    (fun m m1 => 
      forall m2, pstep m m2 -> 
        exists m', pstep m1 m' /\ pstep m2 m') ls ls1 ->
  exists ls', All2 pstep ls1 ls' /\ All2 pstep ls2 ls'.
Proof with eauto using All2.
  move=> p1 p2 h. move: ls2 p1 p2. elim: h=> {ls ls1}.
  move=> ls _ p. inv p.
    exists [::]...
  move=> m m' ls ls' f p ih ls2 p1 p2.
    inv p1.
    inv p2.
    move: H1=> /f[mx[p3 p4]].
    move: (ih _ H4 H5)=> [lsx[p5 p6]].
    exists (mx :: lsx)...
Qed.

Lemma pstep_diamond (m m1 m2 : term) (p : pstep m m1) :
  pstep m m2 -> exists m', pstep m1 m' /\ pstep m2 m'.
Proof with eauto 6 using pstep, pstep_refl, All2, pstep_compat_Beta, pstep_spine.
Proof.
  move: m m1 p m2.
  apply: pstep_ind_nested.
  move=> x m p. inv p. exists (Var x)...
  move=> srt l m p. inv p. exists (Sort srt l)...
  move=> n n' pN ihN m p. inv p.
    move: H0=> /ihN [m' [p2 p3]].
    exists (Lam m')...
  move=> m m' n n' p1 ih1 p2 ih2 m2 p3. inv p3.
    move: H1=> /ih1 [m'1 [p3 p4]].
    move: H3=> /ih2 [m'2 [p5 p6]].
    exists (App m'1 m'2)...
    inv p1.
    have h : pstep (Lam m0) (Lam m'0).
      by constructor.
    move: h=> /ih1 [m' [p3 p4]].
    move: H3=> /ih2 [m'1 [p5 p6]].
    inv p3; inv p4.
    exists (n'2.[m'1/])... 
  move=> m m' n n' p1 ih1 p2 ih2 m2 p3. inv p3.
    inv H1.
    move: H0=> /ih1 [m'0 [p3 p4]].
    move: H3=> /ih2 [m'1 [p5 p6]].
    exists (m'0.[m'1/])...
    move: H1=> /ih1 [m'1 [p3 p4]].
    move: H3=> /ih2 [m'2 [p5 p6]].
    exists (m'1.[m'2/])...
  move=> A A' s B B' p1 ih1 p2 ih2 m2 p3. inv p3.
    move: H3=> /ih1 [m' [p3 p4]].
    move: H4=> /ih2 [m'0 [p5 p6]].
    exists (Prod m' m'0 s)...
  move=> A A' s B B' p1 ih1 p2 ih2 m2 p3. inv p3.
    move: H3=> /ih1 [m' [p3 p4]].
    move: H4=> /ih2 [m'0 [p5 p6]].
    exists (Lolli  m' m'0 s)...
  move=> A A' s Cs Cs' p1 ih1 p2 ih2 m2 p3. inv p3.
    move: H3=> /ih1 [Ax [p4 p5]].
    move: (All2_diamond p2 H4 ih2)=>[lsx[p6 p7]].
    exists (Ind Ax s lsx)...
  move=> i m m' p1 ih m2 p2. inv p2.
    move: H2=> /ih [m'1 [p2 p3]].
    exists (Constr i m'1)...
  move=> m m' Q Q' Fs Fs' p1 ih1 p2 ih2 p3 ih3 m2 p4. inv p4.
    move: H2=> /ih1 [mx [p4 p5]].
    move: H4=> /ih2 [Qx [p6 p7]].
    move: (All2_diamond p3 H5 ih3)=>[lsx [p8 p9]].
    exists (Case mx Qx lsx)...
    move: (pstep_spine_inv p1)=>[hx [msx[e[p4 p5]]]]; subst.
    have pf : pstep (spine (Constr i m0) ms) (spine (Constr i m0) ms').
      apply: pstep_spine...
    move: pf=> /ih1[mx[p6 p7]].
    move: (pstep_spine_inv p6)=>[hx'[msx'[e[p8 p9]]]]; subst.
    move: p7=>/pstep_spine_congr=> px1.
    move: p6=>/pstep_spine_congr=> px2.
    move: (All2_diamond p3 H5 ih3)=>[Fsx[pFxs1 pFxs2]].
    move: (pstep_iget1 pFxs2 H2)=> [Fx[ig pFx]].
    exists (spine Fx msx')...


  move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 ih m2 p4. inv p4.
    have pf :  ~(exists m0 : term, Constr i m = Lam m0).
      move=> [m0 e] //=.
    move: H2=> /pstep_spine_inv H2.
    move: pf=> /H2 [h' [ls' [-> [p4 p5]]]]. inv p4.
    move: (pstep_diamond' _ _ _ p2 H5)=> [ls'0 [p6 p7]].
    move: (pstep_diamond' _ _ _ p1 p5)=> [ls'1 [p8 p9]].
    move: (pstep'_iget1 p6 ig')=> [m'1 [ig1 p10]].
    move: (pstep'_iget2 p7 ig1)=> [m'2 [ig2 p11]].
    exists (spine m'1 ls'1)...
    move: H=> /spine_Constr[e1 [e2 e3]]; subst.
    move: (pstep_diamond' _ _ _ p1 H4)=> [ls'0 [p6 p7]].
    move: (pstep'_iget1 H6 ig)=> [F1 [ig1 p8]].
    move: (iget_iget ig1 H3)=> e; subst.
    move: p8=> /ih[F2 [p9 p10]].
    exists (spine F2 ls'0)...
  move=> m m' Q Q' Fs Fs' p1 ih1 p2 ih2 p3 m2 p4. inv p4.
    move: H2=> /ih1 [m'1 [p4 p5]].
    move: H4=> /ih2 [m'2 [p6 p7]].
    move: (pstep_diamond' _ _ _ p3 H5)=> [ls' [p8 p9]].
    exists (DCase m'1 m'2 ls')...
    have pf :  ~(exists m : term, Constr i m0 = Lam m).
      move=> [m e] //=.
    move: p1=> /pstep_spine_inv p1.
    move: pf=> /p1 [h' [ls'0 [-> [p4 p6]]]]. inv p4. 
    move: (pstep_diamond' _ _ _ H4 p6)=> [ls' [p7 p8]].
    move: (pstep_diamond' _ _ _ p3 H6)=> [ls'1 [p9 p10]].
    move: (pstep'_iget1 p10 H3)=> [F1 [ig1 p11]].
    move: (pstep'_iget2 p9 ig1)=> [F2 [ig2 p12]].
    exists (spine F1 ls')...
  move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 ih m2 p4. inv p4.
    have pf :  ~(exists m0 : term, Constr i m = Lam m0).
      move=> [m0 e] //=.
    move: H2=> /pstep_spine_inv H2.
    move: pf=> /H2 [h' [ls' [-> [p4 p5]]]]. inv p4.
    move: (pstep_diamond' _ _ _ p2 H5)=> [ls'0 [p6 p7]].
    move: (pstep_diamond' _ _ _ p1 p5)=> [ls'1 [p8 p9]].
    move: (pstep'_iget1 p6 ig')=> [m'1 [ig1 p10]].
    move: (pstep'_iget2 p7 ig1)=> [m'2 [ig2 p11]].
    exists (spine m'1 ls'1)...
    move: H=> /spine_Constr[e1 [e2 e3]]; subst.
    move: (pstep_diamond' _ _ _ p1 H4)=> [ls'0 [p6 p7]].
    move: (pstep'_iget1 H6 ig)=> [F1 [ig1 p8]].
    move: (iget_iget ig1 H3)=> e; subst.
    move: p8=> /ih[F2 [p9 p10]].
    exists (spine F2 ls'0)...
  move=> m m' p1 ih m2 p2. inv p2.
    move: H0=> /ih[m3 [p3 p4]].
    exists (Fix m3)...
    move: H0=> /ih[m3 [p3 p4]].
    exists (m3.[Fix m3/])...
  move=> m m' p1 ih m2 p2. inv p2.
    move: H0=> /ih[m3 [p3 p4]].
    exists (m3.[Fix m3/])...
    move: H0=> /ih[m3 [p3 p4]].
    exists (m3.[Fix m3/])...
elim: p ls2=> {ls ls1 pstep_diamond'}.
  move=> ls2 p. inv p.
    exists Nil...
  move=> m1 m2 ls1 ls2 p1 p2 ih ls3 p3. inv p3.
    move: H3=> /ih[ls4 [p4 p5]].
    move: (pstep_diamond _ _ _ H1 p1)=> [m3 [p6 p7]].
    exists (Cons m3 ls4)...
Qed.
      
