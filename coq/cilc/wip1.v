From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CILC.

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

Lemma merge_merge T (Gamma1 Gamma2 Gamma3 Gamma4 Gamma : context T) :
  merge Gamma1 Gamma2 Gamma3 ->
  merge Gamma3 Gamma4 Gamma ->
  exists Gamma5,
    merge Gamma1 Gamma4 Gamma5 /\
    merge Gamma5 Gamma2 Gamma.
Proof with eauto using merge.
  move=> mg. 
  elim: mg Gamma4 Gamma=>{Gamma1 Gamma2 Gamma3}; intros.
  - inv H.
    exists nil...
  - inv H1.
    move: (H0 _ _ H6)=>{H0}[Gamma7[mg1 mg2]].
    exists (m +u Gamma7)...
  - inv H1.
    move: (H0 _ _ H6)=>{H0}[Gamma7[mg1 mg2]].
    exists (m +l Gamma7)...
  - inv H1.
    move: (H0 _ _ H6)=>{H0}[Gamma7[mg1 mg2]].
    exists (+n Gamma7)...
  - inv H1.
    move: (H0 _ _ H3)=>{H3}[Gamma7[mg1 mg2]].
      exists (m +l Gamma7)...
    move: (H0 _ _ H3)=>{H3}[Gamma7[mg1 mg2]].
      exists (+n Gamma7)...
Qed.

Inductive term : Type :=
| Var    (x : var)
| Sort   (s : sort) (l : nat)
| Prod   (A : term) (B : {bind term}) (s : sort)
| Lolli  (A : term) (B : {bind term}) (s : sort)
| Lam    (A : term) (m : {bind term}) (s : sort)
| App    (m n : term)
| Ind    (A : term) (Cs : list {bind term}) (s : sort)
| Constr (i : nat) (m : term)
| Case   (m Q : term) (Fs : list term)
| DCase  (m Q : term) (Fs : list term)
| Fix    (A : term) (m : {bind term}).

Section term_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x).
  Hypothesis ih_Sort : forall s l, P (Sort s l).
  Hypothesis ih_Prod : forall A B s, P A -> P B -> P (Prod A B s).
  Hypothesis ih_Lolli : forall A B s, P A -> P B -> P (Lolli A B s).
  Hypothesis ih_Lam : forall A m s, P A -> P m -> P (Lam A m s).
  Hypothesis ih_App : forall m n, P m -> P n -> P (App m n).
  Hypothesis ih_Ind : forall A Cs s, P A -> List.Forall P Cs -> P (Ind A Cs s).
  Hypothesis ih_Constr : forall i m, P m -> P (Constr i m).
  Hypothesis ih_Case : 
    forall m Q Fs, P m -> P Q -> List.Forall P Fs -> P (Case m Q Fs).
  Hypothesis ih_DCase : 
    forall m Q Fs, P m -> P Q -> List.Forall P Fs -> P (DCase m Q Fs).
  Hypothesis ih_Fix : forall A m, P A -> P m -> P (Fix A m).

  Fixpoint term_ind_nested m : P m.
  Proof.
    pose ih_nested := (
      fix fold xs : List.Forall P xs :=
        match xs with
        | nil => List.Forall_nil _
        | x :: xs => List.Forall_cons _ (term_ind_nested x) (fold xs)
        end).
    case m; intros.
    apply ih_Var.
    apply ih_Sort.
    apply ih_Prod; eauto.
    apply ih_Lolli; eauto.
    apply ih_Lam; eauto.
    apply ih_App; eauto.
    apply ih_Ind; eauto.
    apply ih_Constr; eauto.
    apply ih_Case; eauto.
    apply ih_DCase; eauto.
    apply ih_Fix; eauto.
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

Inductive All2 R : list term -> list term -> Prop :=
| All2_nil : All2 R nil nil
| All2_cons m m' ls ls' :
  R m m' ->
  All2 R ls ls' ->
  All2 R (m :: ls) (m' :: ls').

Inductive All2i R : nat -> list term -> list term -> Prop :=
| All2i_nil i : All2i R i nil nil
| All2i_cons i m m' ls ls' :
  R i m m' ->
  All2i R i.+1 ls ls' ->
  All2i R i (m :: ls) (m' :: ls').

Inductive step : term -> term -> Prop :=
| step_LamL A A' m s :
  step A A' ->
  step (Lam A m s) (Lam A' m s)
| step_LamR A m m' s :
  step m m' ->
  step (Lam A m s) (Lam A m' s)
| step_AppL m m' n :
  step m m' ->
  step (App m n) (App m' n)
| step_AppR m n n' :
  step n n' ->
  step (App m n) (App m n')
| step_Beta A m n s :
  step (App (Lam A m s) n) m.[n/]
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
| step_IndA A A' Cs s :
  step A A' ->
  step (Ind A Cs s) (Ind A' Cs s)
| step_IndCs A Cs Cs' s :
  One2 step Cs Cs' ->
  step (Ind A Cs s) (Ind A Cs' s)
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
| step_FixL A A' m :
  step A A' ->
  step (Fix A m) (Fix A' m)
| step_FixR A m m' :
  step m m' ->
  step (Fix A m) (Fix A m')
| step_FixIota A m :
  step (Fix A m) (m.[Fix A m/]).

Section step_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_LamL : 
    forall A A' m s, step A A' -> P A A' -> P (Lam A m s) (Lam A' m s).
  Hypothesis ih_LamR : 
    forall A m m' s, step m m' -> P m m' -> P (Lam A m s) (Lam A m' s).
  Hypothesis ih_AppL : 
    forall m m' n, step m m' -> P m m' -> P (App m n) (App m' n).
  Hypothesis ih_AppR :
    forall m n n', step n n' -> P n n' -> P (App m n) (App m n').
  Hypothesis ih_Beta : 
    forall A m n s, P (App (Lam A m s) n) m.[n/].
  Hypothesis ih_ProdL :
    forall A A' B s, step A A' -> P A A' -> P (Prod A B s) (Prod A' B s).
  Hypothesis ih_ProdR :
    forall A B B' s, step B B' -> P B B' -> P (Prod A B s) (Prod A B' s).
  Hypothesis ih_LolliL :
    forall A A' B s, step A A' -> P A A' -> P (Lolli A B s) (Lolli A' B s).
  Hypothesis ih_LolliR :
    forall A B B' s, step B B' -> P B B' -> P (Lolli A B s) (Lolli A B' s).
  Hypothesis ih_IndA :
    forall A A' Cs s, step A A' -> P A A' -> P (Ind A Cs s) (Ind A' Cs s).
  Hypothesis ih_IndCs :
    forall A Cs Cs' s, One2 step Cs Cs' -> One2 P Cs Cs' -> 
      P (Ind A Cs s) (Ind A Cs' s).
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
  Hypothesis ih_FixL :
    forall A A' m, step A A' -> P A A' -> P (Fix A m) (Fix A' m).
  Hypothesis ih_FixR :
    forall A m m', step m m' -> P m m' -> P (Fix A m) (Fix A m').
  Hypothesis ih_FixIota :
    forall A m, P (Fix A m) (m.[Fix A m/]).

  Fixpoint step_ind_nested m m' (st : step m m') : P m m'.
  Proof.
    pose ih_nested := (
      fix fold ls1 ls2 (p : One2 step ls1 ls2) : One2 P ls1 ls2 :=
        match p with
        | One2_hd _ _ _ hd => One2_hd _ (step_ind_nested _ _ hd)
        | One2_tl _ _ _ tl => One2_tl _ (fold _ _ tl)
        end).
    case st; intros.
    apply ih_LamL; eauto.
    apply ih_LamR; eauto.
    apply ih_AppL; eauto.
    apply ih_AppR; eauto.
    apply ih_Beta; eauto.
    apply ih_ProdL; eauto.
    apply ih_ProdR; eauto.
    apply ih_LolliL; eauto.
    apply ih_LolliR; eauto.
    apply ih_IndA; eauto.
    apply ih_IndCs; eauto.
    apply ih_Constr; eauto.
    apply ih_CaseM; eauto.
    apply ih_CaseQ; eauto.
    apply ih_CaseFs; eauto.
    apply ih_CaseIota; eauto.
    apply ih_DCaseM; eauto.
    apply ih_DCaseQ; eauto.
    apply ih_DCaseFs; eauto.
    apply ih_DCaseIota; eauto.
    apply ih_FixL; eauto.
    apply ih_FixR; eauto.
    apply ih_FixIota; eauto.
  Qed.
End step_ind_nested.

Inductive pstep : term -> term -> Prop :=
| pstep_Var x :
  pstep (Var x) (Var x)
| pstep_Sort srt l :
  pstep (Sort srt l) (Sort srt l)
| pstep_Lam A A' n n' s : 
  pstep A A' ->
  pstep n n' -> 
  pstep (Lam A n s) (Lam A' n' s)
| pstep_App m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_Beta A m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam A m s) n) (m'.[n'/])
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
| pstep_Ind A A' Cs Cs' s :
  pstep A A' ->
  All2 pstep Cs Cs' ->
  pstep (Ind A Cs s) (Ind A' Cs' s)
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
| pstep_Fix A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fix A m) (Fix A' m')
| pstep_FixIota A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Fix A m) (m'.[Fix A' m'/]).

Section pstep_ind_nested.
  Variable P : term -> term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x) (Var x).
  Hypothesis ih_Sort : forall srt l, P (Sort srt l) (Sort srt l).
  Hypothesis ih_Lam : 
    forall A A' n n' s, pstep A A' -> P A A' -> pstep n n' -> P n n' -> 
      P (Lam A n s) (Lam A' n' s).
  Hypothesis ih_App :
    forall m m' n n', pstep m m' -> P m m' -> pstep n n' -> P n n' -> 
      P (App m n) (App m' n').
  Hypothesis ih_Beta :
    forall A m m' n n' s, pstep m m' -> P m m' -> pstep n n' -> P n n' ->
      P (App (Lam A m s) n) m'.[n'/].
  Hypothesis ih_Prod :
    forall A A' B B' s, pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Prod A B s) (Prod A' B' s).
  Hypothesis ih_Lolli :
    forall A A' B B' s, pstep A A' -> P A A' -> pstep B B' -> P B B' ->
      P (Lolli A B s) (Lolli A' B' s).
  Hypothesis ih_Ind :
    forall A A' Cs Cs' s, 
      pstep A A' -> P A A' -> 
      All2 pstep Cs Cs' -> All2 P Cs Cs' ->
      P (Ind A Cs s) (Ind A' Cs' s).
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
    forall A A' m m', pstep A A' -> P A A' -> pstep m m' -> P m m' -> 
      P (Fix A m) (Fix A' m').
  Hypothesis ih_FixIota :
    forall A A' m m', pstep A A' -> P A A' -> pstep m m' -> P m m' -> 
      P (Fix A m) (m'.[Fix A' m'/]).
  
  Fixpoint pstep_ind_nested m m' (st : pstep m m') : P m m'.
  Proof.
    pose ih_nested := (
      fix fold ls1 ls2 (p : All2 pstep ls1 ls2) : All2 P ls1 ls2 :=
        match p with
        | All2_nil => All2_nil _
        | All2_cons _ _ _ _ hd tl =>
          All2_cons (pstep_ind_nested _ _ hd) (fold _ _ tl)
        end).
    case st; intros.
    apply ih_Var.
    apply ih_Sort.
    apply ih_Lam; eauto.
    apply ih_App; eauto.
    apply ih_Beta; eauto.
    apply ih_Prod; eauto.
    apply ih_Lolli; eauto.
    apply ih_Ind; eauto.
    apply ih_Constr; eauto.
    apply ih_Case; eauto.
    eapply ih_CaseIota; eauto.
    apply ih_DCase; eauto.
    eapply ih_DCaseIota; eauto.
    apply ih_Fix; eauto.
    apply ih_FixIota; eauto.
  Qed.
End pstep_ind_nested.

Notation red := (star step).
Notation "m === n" := (conv step m n) (at level 50).

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

Lemma spine'_Constr_inj i1 i2 h1 h2 ls1 ls2 :
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

Lemma spine_Constr_inj i1 i2 h1 h2 ls1 ls2 :
  spine (Constr i1 h1) ls1 = spine (Constr i2 h2) ls2 ->
    i1 = i2 /\ h1 = h2 /\ ls1 = ls2.
Proof.
  rewrite! spine_spine'_rev=> /spine'_Constr_inj[->[->e]].
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
  move=> A m n s sigma.
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
  move=> A m sigma.
    replace m.[Fix A m/].[sigma] with m.[up sigma].[Fix A.[sigma] m.[up sigma]/]
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

Lemma red_Lam A1 A2 n1 n2 s : 
  red A1 A2 -> red n1 n2 -> red (Lam A1 n1 s) (Lam A2 n2 s).
Proof. 
  move=> A B. apply: (star_trans (Lam A2 n1 s)).
  apply: (star_hom ((Lam^~ n1)^~ s)) A=> x y. exact: step_LamL.
  apply: (star_hom ((Lam A2)^~ s)) B=> x y. exact: step_LamR. 
Qed.

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

Lemma red_Ind A1 A2 Cs1 Cs2 s :
  red A1 A2 -> star (One2 step) Cs1 Cs2 -> 
    red (Ind A1 Cs1 s) (Ind A2 Cs2 s).
Proof.
  move=> A B. 
  apply: (star_trans (Ind A2 Cs1 s)).
  apply: (star_hom ((Ind^~ Cs1)^~ s)) A=> x y. exact: step_IndA.
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

Lemma red_Fix A1 A2 m1 m2 :
  red A1 A2 -> red m1 m2 -> red (Fix A1 m1) (Fix A2 m2).
Proof.
  move=> A B. apply: (star_trans (Fix A2 m1)).
  apply: (star_hom (Fix^~ m1)) A=> x y. exact: step_FixL.
  apply: (star_hom (Fix A2)) B=> x y. exact: step_FixR.
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
  forall x, sigma x === tau x.

Lemma conv_Lam A1 A2 m1 m2 s : 
  A1 === A2 -> m1 === m2 -> Lam A1 m1 s === Lam A2 m2 s.
Proof. 
  move=> A B.
  apply: (conv_trans (Lam A2 m1 s)).
  apply: (conv_hom ((Lam^~ m1)^~ s)) A=> x y. exact: step_LamL.
  apply: (conv_hom ((Lam A2)^~ s)) B=> x y. exact: step_LamR.
Qed.

Lemma conv_Prod A1 A2 s B1 B2 :
  A1 === A2 -> B1 === B2 -> Prod A1 B1 s === Prod A2 B2 s.
Proof.
  move=> A B.
  apply: (conv_trans (Prod A2 B1 s)).
  apply: (conv_hom ((Prod^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Prod A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_Lolli A1 A2 s B1 B2 :
  A1 === A2 -> B1 === B2 -> Lolli A1 B1 s === Lolli A2 B2 s.
Proof.
  move=> A B.
  apply: (conv_trans (Lolli A2 B1 s)).
  apply: (conv_hom ((Lolli^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Lolli A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_App m1 m2 n1 n2 :
  m1 === m2 -> n1 === n2 -> App m1 n1 === App m2 n2.
Proof.
  move=> A B.
  apply: (conv_trans (App m2 n1)).
  apply: (conv_hom (App^~ n1)) A=> x y ps.
    by constructor.
  apply: conv_hom B=> x y ps.
    by constructor.
Qed.

Lemma conv_Ind A1 A2 Cs1 Cs2 s :
  A1 === A2 -> conv (One2 step) Cs1 Cs2 -> Ind A1 Cs1 s === Ind A2 Cs2 s.
Proof.
  move=> A B. 
  apply: (conv_trans (Ind A2 Cs1 s)).
  apply: (conv_hom ((Ind^~ Cs1)^~ s)) A=> x y. exact: step_IndA.
  elim: B=> //.
    move=> y z cv' cv st.
    apply: (conv_trans (Ind A2 y s)).
      by apply: cv.
      by apply: conv1; eauto using step.
    move=> y z cv' cv st.
    apply: (conv_trans (Ind A2 y s)).
      by apply: cv.
      by apply: conv1i; eauto using step.
Qed.

Lemma conv_Constr i m1 m2 :
  m1 === m2 -> Constr i m1 === Constr i m2.
Proof.
  move=> A.
  apply: (conv_hom (Constr i)) A => x y. exact: step_Constr.
Qed.

Lemma conv_Case m1 m2 Q1 Q2 Fs1 Fs2 :
  m1 === m2 -> 
  Q1 === Q2 -> 
  conv (One2 step) Fs1 Fs2 -> 
  Case m1 Q1 Fs1 === Case m2 Q2 Fs2.
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
  m1 === m2 -> 
  Q1 === Q2 -> 
  conv (One2 step) Fs1 Fs2 -> 
  DCase m1 Q1 Fs1 === DCase m2 Q2 Fs2.
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

Lemma conv_Fix A1 A2 m1 m2 :
  A1 === A2 -> m1 === m2 -> Fix A1 m1 === Fix A2 m2.
Proof.
  move=> A B.
  apply: (conv_trans (Fix A2 m1)).
  apply: (conv_hom (Fix^~ m1)) A=> x y. exact: step_FixL.
  apply: (conv_hom (Fix A2)) B=> x y. exact: step_FixR.
Qed.

Lemma conv_hd h1 h2 ls :
  h1 === h2 -> conv (One2 step) (h1 :: ls) (h2 :: ls).
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
  h === h' ->
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
  m === n -> m.[sigma] === n.[sigma].
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
  sconv sigma tau -> s.[sigma] === s.[tau].
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

Lemma conv_Beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof.
  move: s.
  apply: term_ind_nested; eauto using pstep. 
  move=> A Cs s pA ih.
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
  move=> A m m' n n' s p1 r1 p2 r2.
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
  move=> A A' m m' pA rA pM rM.
    apply: star_trans.
    apply: red_Fix.
    exact: rA.
    exact: rM.
    apply: star1.
    by constructor.
Qed.

Lemma pstep_subst sigma m m' :
  pstep m m' -> pstep m.[sigma] m'.[sigma].
Proof with eauto using pstep, pstep_refl, All2, All2_pstep_refl.
  move=> p. move: m m' p sigma.
  apply: pstep_ind_nested...
  move=> A m m' n n' s p1 ih1 p2 ih2 sigma; asimpl.
    pose proof (ih1 (up sigma))=> {ih1}.
    pose proof (ih2 sigma)=> {ih2}.
    pose proof (pstep_Beta A.[sigma] s H H0).
    by asimpl in H1.
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
  move=> A A' m m' pA ihA pM ihM sigma; asimpl.
    replace m'.[Fix A'.[sigma] m'.[up sigma] .: sigma]
      with (m'.[up sigma]).[Fix A'.[sigma] m'.[up sigma]/]
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
  move=> A m m' n n' s pM ihM pN ihN sigma tau pss; asimpl.
    have pss' := psstep_up pss.
    have hM := ihM _ _ pss'.
    have hN := ihN _ _ pss.
    pose proof (pstep_Beta (A.[sigma]) s hM hN).
    by asimpl in H.
  move=> A A' Cs Cs' s pA ihA pCs ihCs sigma tau pss; asimpl.
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
  move=> A A' m m' pA ihA pM ihM sigma tau ps; asimpl.
    replace m'.[Fix A'.[tau] m'.[up tau] .: tau]
      with (m'.[up tau]).[Fix A'.[tau] m'.[up tau]/]
      by autosubst.
    constructor.
    exact: ihA.
    apply: ihM.
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
  All2 pstep ls ls' -> iget i ls m -> 
    exists m', iget i ls' m' /\ pstep m m'.
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
  All2 pstep ls ls' -> iget i ls' m' -> 
    exists m, iget i ls m /\ pstep m m'.
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

Lemma spine_Lam_Constr_False A m s i h ls :
  ~Lam A m s = spine' (Constr i h) ls.
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

Lemma All2_pstep_append ls1 ls2 ls1' ls2' :
  All2 pstep ls1 ls2 -> All2 pstep ls1' ls2' ->
    All2 pstep (ls1 ++ ls1') (ls2 ++ ls2').
Proof with eauto using All2.
  move=> p. elim: p ls1' ls2'=> //={ls1 ls2}...
Qed.

Lemma All2_pstep_rev ls1 ls2 :
  All2 pstep ls1 ls2 -> All2 pstep (rev ls1) (rev ls2).
Proof with eauto using All2.
  elim=> //={ls1 ls2}...
  move=> m m' ls ls' p1 p2 p3.
    replace (m :: ls) with ([:: m] ++ ls) by eauto.
    replace (m' :: ls') with ([:: m'] ++ ls') by eauto.
    rewrite! rev_cat.
    apply All2_pstep_append...
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
  apply All2_pstep_rev in p2.
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
  rewrite! revK=> /All2_pstep_rev.
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
Proof with eauto 6 using 
  pstep, pstep_refl, All2, pstep_compat_Beta, pstep_spine.
Proof.
  move: m m1 p m2.
  apply: pstep_ind_nested.
  move=> x t p. inv p. exists (Var x)...
  move=> srt l m p. inv p. exists (Sort srt l)...
  move=> A A' n n' s pA ihA pN ihN m p. inv p.
    move: H3=> /ihA[Ax [pAx1 pAx2]].
    move: H4=> /ihN [nx [nx1 nx2]].
    exists (Lam Ax nx s)...
  move=> m m' n n' pM ihM pN ihN t p. inv p.
    move: H1=> /ihM [mx [pMx1 pM2]].
    move: H3=> /ihN [nx [pNx1 pNx2]].
    exists (App mx nx)...
    inv pM.
    have pLam : pstep (Lam A m0 s) (Lam A' m'0 s).
      by constructor.
    move: pLam=> /ihM [mx [pMx1 pMx2]].
    move: H3=> /ihN [nx [pNx1 pNx2]].
    inv pMx1; inv pMx2.
    exists (n'2.[nx/])...
  move=> A m m' n n' s pM ihM pN ihN t p. inv p.
    inv H1.
    move: H6=> /ihM [mx [pMx1 pMx2]].
    move: H3=> /ihN [nx [pNx1 pNx2]].
    exists (mx.[nx/])...
    move: H4=> /ihM [mx [pMx1 pMx2]].
    move: H5=> /ihN [nx [pNx1 pNx2]].
    exists (mx.[nx/])...
  move=> A A' B B' s pA ihA pB ihB t p. inv p.
    move: H3=> /ihA [Ax [pAx1 pAx2]].
    move: H4=> /ihB [Bx [pBx1 pBx2]].
    exists (Prod Ax Bx s)...
  move=> A A' B B' s pA ihA pB ihB t p. inv p.
    move: H3=> /ihA [Ax [pAx1 pAx2]].
    move: H4=> /ihB [Bx [pBx1 pBx2]].
    exists (Lolli Ax Bx s)...
  move=> A A' Cs Cs' s pA ihA pCs ihCs t p. inv p.
    move: H3=> /ihA [Ax [pAx1 pAx2]].
    move: (All2_diamond pCs H4 ihCs)=>[Csx[pCsx1 pCsx2]].
    exists (Ind Ax Csx s)...
  move=> i m m' pM ihM t p. inv p.
    move: H2=> /ihM [mx [pMx1 pMx2]].
    exists (Constr i mx)...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs t p. inv p.
    move: H2=> /ihM [mx [pMx1 pMx2]].
    move: H4=> /ihQ [Qx [pQx1 pQx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx [pFsx1 pFsx2]].
    exists (Case mx Qx Fsx)...
    move: (pstep_spine_inv pM)=>[hx [msx[e[pM0 pMs]]]]; subst.
    have pf : pstep (spine (Constr i m0) ms) (spine (Constr i m0) ms').
      apply: pstep_spine...
    move: pf=> /ihM[mx[pMx1 pMx2]].
    move: (pstep_spine_inv pMx1)=>[hx'[msx'[e[pHx pMsx]]]]; subst.
    move: pMx2=>/pstep_spine_congr=> pMs'.
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFxs1 pFxs2]].
    move: (pstep_iget1 pFxs2 H2)=> [Fx[ig pFx]].
    exists (spine Fx msx')...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs t p. inv p.
    move: H2=>/pstep_spine_inv[hx[mx[->[pM pMs']]]].
    move: (All2_diamond pMs pMs' ihMs)=>[mx'[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    exists (spine Fx mx')...
    move: H=> /spine_Constr_inj[e1[e2 e3]]; subst.
    move: (All2_diamond pMs H4 ihMs)=>[mx[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    move: (pstep_iget2 pFsx2 igFx)=>[Fx'[igFx' pFx']].
    move: (iget_iget igFx' H2)=>e; subst.
    exists (spine Fx mx)...
  move=> m m' Q Q' Fs Fs' pM ihM pQ ihQ pFs ihFs t p. inv p.
    move: H2=> /ihM [mx [pMx1 pMx2]].
    move: H4=> /ihQ [Qx [pQx1 pQx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx [pFsx1 pFsx2]].
    exists (DCase mx Qx Fsx)...
    move: (pstep_spine_inv pM)=>[hx [msx[e[pM0 pMs]]]]; subst.
    have pf : pstep (spine (Constr i m0) ms) (spine (Constr i m0) ms').
      apply: pstep_spine...
    move: pf=> /ihM[mx[pMx1 pMx2]].
    move: (pstep_spine_inv pMx1)=>[hx'[msx'[e[pHx pMsx]]]]; subst.
    move: pMx2=>/pstep_spine_congr=> pMs'.
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFxs1 pFxs2]].
    move: (pstep_iget1 pFxs2 H2)=> [Fx[ig pFx]].
    exists (spine Fx msx')...
  move=> i m ms ms' Q Fs Fs' F' ig pMs ihMs pFs ihFs t p. inv p.
    move: H2=>/pstep_spine_inv[hx[mx[->[pM pMs']]]].
    move: (All2_diamond pMs pMs' ihMs)=>[mx'[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    exists (spine Fx mx')...
    move: H=> /spine_Constr_inj[e1[e2 e3]]; subst.
    move: (All2_diamond pMs H4 ihMs)=>[mx[pMx1 pMx2]].
    move: (All2_diamond pFs H5 ihFs)=>[Fsx[pFsx1 pFsx2]].
    move: (pstep_iget1 pFsx1 ig)=>[Fx[igFx pFx]].
    move: (pstep_iget2 pFsx2 igFx)=>[Fx'[igFx' pFx']].
    move: (iget_iget igFx' H2)=>e; subst.
    exists (spine Fx mx)...
  move=> A A' m m' pA ihA pM ihM t p. inv p.
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (Fix Ax mx)...
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (mx.[Fix Ax mx/])...
  move=> A A' m m' pA ihA pM ihM t p. inv p.
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (mx.[Fix Ax mx/])...
    move: H1=> /ihA[Ax[pAx1 pAx2]].
    move: H3=> /ihM[mx[pMx1 pMx2]].
    exists (mx.[Fix Ax mx/])...
Qed.

Lemma strip m m1 m2 (p : pstep m m1) :
  red m m2 -> exists m', red m1 m' /\ pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=> rd. elim: rd m1 p=>{m2}...
  move=> y z rM ih /step_pstep p1 t /ih[x[r1 p2]].
  move: (pstep_diamond p1 p2)=>[w[pW1 pW2]].
  exists w. split...
  apply: star_trans; eauto.
  exact: pstep_red.
Qed.

Theorem confluence : confluent step.
Proof with eauto using step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r1 r2.
  elim: r1 z r2=>{y}.
  move=> z r.
    exists z...
  move=> y z1 r1 ih s z2 /ih[z3 r2].
    move: s=> /step_pstep p1 p2.
    move: (strip p1 r2)=>[mx[rMx1 rMx2]].
    exists mx...
    apply: star_trans...
    exact: pstep_red.
Qed.
Hint Resolve confluence.

Theorem church_rosser : CR step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.
Hint Resolve church_rosser.

Lemma red_Sort_inv s l A :
  red (Sort s l) A -> A = Sort s l.
Proof.
  elim; eauto.
  move=> y z r e st; subst.
  inv st; eauto.
Qed.

Lemma red_Prod_inv A B s x :
  red (Prod A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Prod A' B' s.
Proof.
  elim; eauto.
  move=> y z rd [A'[B'[rA[rB e]]]] st; subst.
  inv st.
  exists A'0. exists B'. firstorder.
    apply: star_trans; eauto.
    exact: star1.
  exists A'. exists B'0. firstorder.
    apply: star_trans; eauto.
    exact: star1.
Qed.

Lemma red_Lolli_inv A B s x :
  red (Lolli A B s) x -> 
  exists A' B',
    red A A' /\
    red B B' /\
    x = Lolli A' B' s.
Proof.
  elim; eauto.
  move=> y z rd [A'[B'[rA[rB e]]]] st; subst.
  inv st.
  exists A'0. exists B'. firstorder.
    apply: star_trans; eauto.
    exact: star1.
  exists A'. exists B'0. firstorder.
    apply: star_trans; eauto.
    exact: star1.
Qed.

Lemma red_Var_inv x y :
  red (Var x) y -> y = Var x.
Proof.
  elim; eauto.
  move=> y' z rd e s; subst. inv s.
Qed.

Lemma red_Lam_inv A m s n :
  red (Lam A m s) n ->
  exists A' m',
    red A A' /\ red m m' /\ n = Lam A' m' s.
Proof.
  elim.
  by exists A; exists m.
  move=> y z rd [A'[m'[rA[rM e]]]] st; subst.
  inv st.
  exists A'0. exists m'. repeat constructor; eauto using star.
  exists A'. exists m'0. repeat constructor; eauto using star.
Qed.

Lemma red_Ind_inv A Cs s n :
  red (Ind A Cs s) n ->
  exists A' Cs',
    red A A' /\ 
    star (One2 step) Cs Cs' /\ 
    n = Ind A' Cs' s.
Proof.
  elim.
  exists A. exists Cs. repeat constructor.
  move=> y z rd [A'[Cs'[rA[rCs e]]]] st; subst.
  inv st.
  exists A'0. exists Cs'. repeat constructor; eauto using star.
  exists A'. exists Cs'0. repeat constructor; eauto using star.
Qed.

Lemma red_Constr_inv i m n :
  red (Constr i m) n ->
  exists m',
    red m m' /\ n = Constr i m'.
Proof.
  elim.
  exists m. repeat constructor.
  move=> y z rd [m'[rM e]] st; subst.
  inv st.
  exists m'0. repeat constructor; eauto using star.
Qed.

Lemma Sort_inj s1 s2 l1 l2 :
  Sort s1 l1 === Sort s2 l2 ->
  s1 = s2 /\ l1 = l2.
Proof.
  move=> /church_rosser h. inv h.
  move: H=> /red_Sort_inv e; subst.
  move: H0=> /red_Sort_inv [->->]; eauto.
Qed.

Lemma Prod_inj A A' B B' s s' :
  Prod A B s === Prod A' B' s' ->
  A === A' /\ B === B' /\ s = s'.
Proof.
  move=> /church_rosser h. inv h.
  move: H=> /red_Prod_inv[Ax[Bx[rA[rB e]]]]; subst.
  move: H0=> /red_Prod_inv[Ax'[Bx'[rA'[rB' [e1 e2]]]]] ->; subst.
  firstorder; eauto using join_conv.
Qed.

Lemma Lolli_inj A A' B B' s s' :
  Lolli A B s === Lolli A' B' s' ->
  A === A' /\ B === B' /\ s = s'.
Proof.
  move=> /church_rosser h. inv h.
  move: H=> /red_Lolli_inv[Ax[Bx[rA[rB e]]]]; subst.
  move: H0=> /red_Lolli_inv[Ax'[Bx'[rA'[rB' [e1 e2]]]]] ->; subst.
  firstorder; eauto using join_conv.
Qed.

Ltac red_inv m H :=
  match m with
  | Var    => apply red_Var_inv in H
  | Sort   => apply red_Sort_inv in H
  | Prod   => apply red_Prod_inv in H
  | Lolli  => apply red_Lolli_inv in H
  | Lam    => apply red_Lam_inv in H
  | Ind    => apply red_Ind_inv in H
  | Constr => apply red_Constr_inv in H
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
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  | [ H : value (App _ _) |- _ ] => inv H
  end; eauto.

Notation "s @ l" := (Sort s l) (at level 30).

Inductive sub1 : term -> term -> Prop :=
| sub1_refl A : 
  sub1 A A
| sub1_Sort s l1 l2 : 
  l1 <= l2 -> 
  sub1 (s @ l1) (s @ l2)
| sub1_Prod A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (Prod A B1 s) (Prod A B2 s)
| sub1_Lolli A B1 B2 s : 
  sub1 B1 B2 -> 
  sub1 (Lolli A B1 s) (Lolli A B2 s).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : 
  sub1 A' B' -> A === A' -> B' === B -> sub A B.
Notation "A <: B" := (sub A B) (at level 50, no associativity) : cilc_scope.

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_Sort s n m : n <= m -> s @ n <: s @ m.
Proof. move=> leq. exact/sub1_sub/sub1_Sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto 6 using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D=>{A B}
    [ A C D 
    | s l1 l2 leq C D conv sb
    | A B1 B2 s sb1 ih C D conv sb2
    | A B1 B2 s sb1 ih C D conv sb2 ]...
  inv sb; try (exfalso; solve_conv)...
    move: conv => /Sort_inj [->eq].
    apply: sub_Sort. subst.
    exact: leq_trans leq _.
  inv sb2; try (exfalso; solve_conv)...
    move: conv => /Prod_inj[conv1 [conv2 ->]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    eapply SubI.
    eapply sub1_Prod...
    eapply conv_Prod...
    exact: conv_Prod.
  inv sb2; try (exfalso; solve_conv)...
    move: conv => /Lolli_inj[conv1 [conv2 ->]].
    move: (ih _ _ conv2 H) => {ih} sub. inv sub.
    eapply SubI. 
    eapply sub1_Lolli...
    eapply conv_Lolli...
    exact: conv_Lolli.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_Sort_inv s1 s2 l1 l2 :
  s1 @ l1 <: s2 @ l2 -> s1 = s2 /\ l1 <= l2.
Proof.
  move=> [s1' s2' []].
  move=> A c1 c2.
    have{c1 c2}/Sort_inj[s l]: s1 @ l1 === s2 @ l2.
      exact: conv_trans c2.
    inv l=> //.
  move=> s l0 l3 leq /Sort_inj[->->] /Sort_inj[<-<-] => //.
  move=> *. exfalso; solve_conv.
  move=> *. exfalso; solve_conv.
Qed.

Lemma sub_Sort_False1 l1 l2 : ~Sort U l1 <: Sort L l2.
Proof.
  move=> [s1 s2 []].
  move=> A e1 e2.
    have e : Sort U l1 === Sort L l2.
      exact: conv_trans e2.
    solve_conv.
  move=> s l3 l4 _ /Sort_inj[<- _] h. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
Qed.

Lemma sub_Sort_False2 l1 l2 : ~Sort L l1 <: Sort U l2.
Proof.
  move=> [s1 s2 []].
  move=> A e1 e2.
    have e : Sort L l1 === Sort U l2.
      exact: conv_trans e2.
    solve_conv.
  move=> s l3 l4 _ /Sort_inj[<- _] h. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
  move=> A B1 B2 s _ e1 e2. solve_conv.
Qed.

Lemma sub_Prod_inv A1 A2 s1 s2 B1 B2 :
  Prod A1 B1 s1 <: Prod A2 B2 s2 -> 
  A1 === A2 /\ B1 <: B2 /\ s1 = s2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. 
    have{c1 c2}/Prod_inj[c1 [c2 ->]]: 
      Prod A1 B1 s1 === Prod A2 B2 s2.
     exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  - move=> *. exfalso; solve_conv.
  - move=> A B0 B3 s sb /Prod_inj[c1 [c2 <-]]. 
    move=> /Prod_inj[c3 [c4 ->]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
  - move=> *. exfalso; solve_conv.
Qed.

Lemma sub_Lolli_inv A1 A2 s1 s2 B1 B2 :
  Lolli A1 B1 s1 <: Lolli A2 B2 s2 -> 
  A1 === A2 /\ B1 <: B2 /\ s1 = s2.
Proof.
  move=> [A' B' []].
  move=> C c1 c2. 
    have{c1 c2}/Lolli_inj[c1 [c2 ->]]: 
      Lolli A1 B1 s1 === Lolli A2 B2 s2.
      exact: conv_trans c2.
    firstorder=>//. exact: conv_sub.
  move=> *. exfalso; solve_conv.
  move=> *. exfalso; solve_conv.
  move=> A B0 B3 s sb /Lolli_inj[c1 [c2 <-]]. 
    move=> /Lolli_inj[c3 [c4 ->]]. 
    firstorder.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst sigma A B : sub1 A B -> sub1 A.[sigma] B.[sigma].
Proof. move=> s. elim: s sigma => /=; eauto using sub1. Qed.

Lemma sub_subst sigma A B : A <: B -> A.[sigma] <: B.[sigma].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

Lemma sub_ren A B xi : A <: B -> A.[ren xi] <: B.[ren xi].
Proof. move=> *; by apply: sub_subst. Qed.

Inductive arity (s : sort) : term -> Prop :=
| arity_Sort l : arity s (Sort s l)
| arity_Prod A B :
  arity s B -> arity s (Prod A B U).

Inductive noccurs : var -> term -> Prop :=
| noccurs_Var x y : ~x = y -> noccurs x (Var y)
| noccurs_Sort x s l : noccurs x (Sort s l)
| noccurs_Prod x A B s :
  noccurs x A -> noccurs x.+1 B -> noccurs x (Prod A B s)
| noccurs_Lolli x A B s :
  noccurs x A -> noccurs x.+1 B -> noccurs x (Lolli A B s)
| noccurs_Lam x A m s :
  noccurs x A -> noccurs x.+1 m -> noccurs x (Lam A m s)
| noccurs_App x m n :
  noccurs x m -> noccurs x n -> noccurs x (App m n)
| noccurs_Ind x A Cs s :
  noccurs x A -> List.Forall (noccurs x.+1) Cs -> noccurs x (Ind A Cs s)
| noccurs_Constr x i m :
  noccurs x m -> noccurs x (Constr i m)
| noccurs_Case x m Q Fs :
  noccurs x m -> noccurs x Q -> List.Forall (noccurs x) Fs ->
    noccurs x (Case m Q Fs)
| noccurs_DCase x m Q Fs :
  noccurs x m -> noccurs x Q -> List.Forall (noccurs x) Fs ->
    noccurs x (DCase m Q Fs)
| noccurs_Fix x A m :
  noccurs x A -> noccurs x.+1 m -> noccurs x (Fix A m).

Section noccurs_ind_nested.
  Variable P : var -> term -> Prop.
  Hypothesis ih_Var : forall x y, ~x = y -> P x (Var y).
  Hypothesis ih_Sort : forall x s l, P x (Sort s l).
  Hypothesis ih_Prod : forall x A B s,
    noccurs x A -> P x A -> noccurs x.+1 B -> P x.+1 B -> P x (Prod A B s).
  Hypothesis ih_Lolli : forall x A B s,
    noccurs x A -> P x A -> noccurs x.+1 B -> P x.+1 B -> P x (Lolli A B s).
  Hypothesis ih_Lam : forall x A m s,
    noccurs x A -> P x A -> noccurs x.+1 m -> P x.+1 m -> P x (Lam A m s).
  Hypothesis ih_App : forall x m n,
    noccurs x m -> P x m -> noccurs x n -> P x n -> P x (App m n).
  Hypothesis ih_Ind : forall x A Cs s,
    noccurs x A -> P x A ->
    List.Forall (noccurs x.+1) Cs -> List.Forall (P x.+1) Cs ->
    P x (Ind A Cs s).
  Hypothesis ih_Constr : forall x i m,
    noccurs x m -> P x m -> P x (Constr i m).
  Hypothesis ih_Case : forall x m Q Fs,
    noccurs x m -> P x m -> 
    noccurs x Q -> P x Q ->
    List.Forall (noccurs x) Fs -> List.Forall (P x) Fs ->
    P x (Case m Q Fs).
  Hypothesis ih_DCase : forall x m Q Fs,
    noccurs x m -> P x m -> 
    noccurs x Q -> P x Q ->
    List.Forall (noccurs x) Fs -> List.Forall (P x) Fs ->
    P x (DCase m Q Fs).
  Hypothesis ih_Fix : forall x A m,
    noccurs x A -> P x A ->
    noccurs x.+1 m -> P x.+1 m ->
    P x (Fix A m).

  Fixpoint noccurs_ind_nested x m (no : noccurs x m) : P x m.
  Proof.
    pose ih_nested := (
      fix fold x ls (no : List.Forall (noccurs x) ls) : List.Forall (P x) ls :=
        match no with
        | List.Forall_nil => List.Forall_nil _
        | List.Forall_cons _ _ pfHd pfTl =>
          List.Forall_cons _ (noccurs_ind_nested x _ pfHd) (fold x _ pfTl)
        end).
    case no; intros.
    apply ih_Var; eauto.
    apply ih_Sort; eauto.
    apply ih_Prod; eauto.
    apply ih_Lolli; eauto.
    apply ih_Lam; eauto.
    apply ih_App; eauto.
    apply ih_Ind; eauto.
    apply ih_Constr; eauto.
    apply ih_Case; eauto.
    apply ih_DCase; eauto.
    apply ih_Fix; eauto.
  Qed.
End noccurs_ind_nested.

Inductive pos : var -> term -> Prop :=
| pos_X x ms : List.Forall (noccurs x) ms -> pos x (spine (Var x) ms)
| pos_Prod x A B s : noccurs x A -> pos x.+1 B -> pos x (Prod A B s)
| pos_Lolli x A B s : noccurs x A -> pos x.+1 B -> pos x (Lolli A B s).

Inductive active : var -> term -> Prop :=
| active_X x ms : List.Forall (noccurs x) ms -> active x (spine (Var x) ms)
| active_Pos x A B s :
  pos x A -> active x.+1 B -> noccurs 0 B -> active x (Lolli A B s)
| active_Lolli x A B s :
  noccurs x A -> active x.+1 B -> active x (Lolli A B s).

Inductive constr : var -> sort -> term -> Prop :=
| constr_X x s ms : 
  List.Forall (noccurs x) ms -> constr x s (spine (Var x) ms)
| constr_UPos x A B :
  pos x A -> constr x.+1 U B -> noccurs 0 B -> constr x U (Prod A B U)
| constr_UProd x A B :
  noccurs x A -> constr x.+1 U B -> constr x U (Prod A B U)
| constr_LPos1 x A B :
  pos x A-> constr x.+1 L B -> noccurs 0 B -> constr x L (Prod A B U)
| constr_LPos2 x A B :
  pos x A -> active x.+1 B -> noccurs 0 B -> constr x L (Prod A B L)
| constr_LProd1 x A B :
  noccurs x A -> constr x.+1 L B -> constr x L (Prod A B U)
| constr_LProd2 x A B :
  noccurs x A -> active x.+1 B -> constr x L (Prod A B L).

Notation prop := (Sort U None).

Fixpoint arity1 (s : sort) (A : term) : term :=
  match A with
  | Sort _ l => Sort s l
  | Prod A B t =>
    Prod A (arity1 s B) t
  | _ => A
  end.

Fixpoint arity2 (s : sort) (I : term) (A : term) : term :=
  match A with
  | Sort _ l => Prod I (Sort s l) U
  | Prod A B t =>
    Prod A (arity2 s (App I.[ren (+1)] (Var 0)) B) t
  | _ => A
  end.

Fixpoint respine hd sp : term :=
  match sp with
  | Prod A B s => Lolli A (respine hd.[ren (+1)] B) s
  | Lolli A B s => Lolli A (respine hd.[ren (+1)] B) s
  | App m n => App (respine hd m) n
  | _ => hd
  end.

Fixpoint drespine hd c sp : term :=
  match sp with
  | Prod A B s => 
    Lolli A (drespine hd.[ren (+1)] (App c.[ren (+1)] (Var 0)) B) s
  | _ => App (respine hd sp) c
  end.

Definition case I Q C : term :=
  respine Q C.[I/].

Definition dcase I Q (c C : term) : term :=
  drespine Q c C.[I/].

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- m :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| u_Sort Gamma s l : 
  pure Gamma ->
  [ Gamma |- s @ l :- U @ l.+1 ]
| u_Prod Gamma A B s l :
  pure Gamma ->
  [ Gamma |- A :- U @ l ] ->
  [ A +u Gamma |- B :- s @ l ] ->
  [ Gamma |- Prod A B U :- U @ l ]
| l_Prod Gamma A B s l :
  pure Gamma ->
  [ Gamma |- A :- L @ l ] ->
  [ +n Gamma |- B :- s @ l ] ->
  [ Gamma |- Prod A B L :- U @ l ]
| u_Lolli Gamma A B s l :
  pure Gamma ->
  [ Gamma |- A :- U @ l ] ->
  [ A +u Gamma |- B :- s @ l ] ->
  [ Gamma |- Lolli A B U :- L @ l ]
| l_Lolli Gamma A B s l :
  pure Gamma ->
  [ Gamma |- A :- L @ l ] ->
  [ +n Gamma |- B :- s @ l ] ->
  [ Gamma |- Lolli A B L :- L @ l ]
| u_Var Gamma x A : 
  hasU Gamma x A ->
  [ Gamma |- Var x :- A ]
| l_Var Gamma x A :
  hasL Gamma x A ->
  [ Gamma |- Var x :- A ]
| u_Lam Gamma n A B s t l :
  pure Gamma ->
  [ Gamma |- Prod A B s :- Sort t l ] ->
  [ A +{s} Gamma |- n :- B ] ->
  [ Gamma |- Lam A n s :- Prod A B s ]
| l_Lam Gamma n A B s t l :
  [ re Gamma |- Lolli A B s :- Sort t l ] ->
  [ A +{s} Gamma |- n :- B ] ->
  [ Gamma |- Lam A n s :- Lolli A B s ]
| u_Prod_App Gamma1 Gamma2 Gamma A B m n :
  pure Gamma2 ->
  [ Gamma1 |- m :- Prod A B U ] ->
  [ Gamma2 |- n :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B.[n/] ]
| l_Prod_App Gamma1 Gamma2 Gamma  A B m n :
  [ Gamma1 |- m :- Prod A B L ] ->
  [ Gamma2 |- n :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B.[n/] ]
| u_Lolli_App Gamma1 Gamma2 Gamma A B m n :
  pure Gamma2 ->
  [ Gamma1 |- m :- Lolli A B U ] ->
  [ Gamma2 |- n :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B.[n/] ]
| l_Lolli_App Gamma1 Gamma2 Gamma A B m n :
  [ Gamma1 |- m :- Lolli A B L ] ->
  [ Gamma2 |- n :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- App m n :- B.[n/] ]
| s_Ind Gamma A s Cs l :
  arity s A ->
  List.Forall (constr 0 s) Cs ->
  pure Gamma ->
  [ Gamma |- A :- Sort U l ] ->
  List.Forall (fun C => [ A +u Gamma |- C :- Sort U l ]) Cs ->
  [ Gamma |- Ind A Cs s :- A ]
| s_Constr Gamma A s i C Cs :
  let I := Ind A Cs s in
  iget i Cs C ->
  pure Gamma ->
  [ Gamma |- I :- A ] ->
  [ Gamma |- Constr i I :- C.[I/] ]
| s_Case Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms :
  let I := Ind A Cs s in
  arity s A ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma1 |- m :- spine I ms ] ->
  [ re Gamma2 |- Q :- arity1 s' A ] ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Gamma2 |- F :- case I Q C ]) Fs Cs ->
  [ Gamma |- Case m Q Fs :- spine Q ms ]
| s_DCase Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms :
  let I := Ind A Cs U in
  arity s A ->
  pure Gamma1 ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma1 |- m :- spine I ms ] ->
  [ re Gamma2 |- Q :- arity2 s' I A ] ->
  All2i (fun i F C =>
    constr 0 U C /\
    [ Gamma2 |- F :- dcase I Q (Constr i I) C ]) 0 Fs Cs ->
  [ Gamma |- DCase m Q Fs :- App (spine Q ms) m ]
| u_Fix Gamma A m l :
  pure Gamma ->
  [ Gamma |- A :- Sort U l ] ->
  [ A +u Gamma |- m :- A.[ren (+1)] ] ->
  [ Gamma |- Fix A m :- A ]
| s_Conv Gamma A B m s l :
  A <: B ->
  [ re Gamma |- B :- Sort s l ] ->
  [ Gamma |- m :- A ] ->
  [ Gamma |- m :- B ]
where "[ Gamma |- m :- A ]" := (has_type Gamma m A).

Section has_type_nested_ind.
  Variable P : context term -> term -> term -> Prop.
  Hypothesis ih_u_Sort : forall Gamma s l, 
    pure Gamma -> P Gamma (s @ l) (U @ l.+1).
  Hypothesis ih_u_Prod : forall Gamma A B s l,
    pure Gamma ->
    [ Gamma |- A :- U @ l ] -> P Gamma A (U @ l) ->
    [ A +u Gamma |- B :- s @ l ] -> P (A +u Gamma) B (s @ l) ->
    P Gamma (Prod A B U) (U @ l).
  Hypothesis ih_l_Prod : forall Gamma A B s l,
    pure Gamma ->
    [ Gamma |- A :- L @ l] -> P Gamma A (L @ l) ->
    [ +n Gamma |- B :- s @ l ] -> P (+n Gamma) B (s @ l) ->
    P Gamma (Prod A B L) (U @ l).
  Hypothesis ih_u_Lolli : forall Gamma A B s l,
    pure Gamma ->
    [ Gamma |- A :- U @ l ] -> P Gamma A (U @ l) ->
    [ A +u Gamma |- B :- s @ l ] -> P (A +u Gamma) B (s @ l) ->
    P Gamma (Lolli A B U) (L @ l). 
  Hypothesis ih_l_Lolli : forall Gamma A B s l,
    pure Gamma ->
    [ Gamma |- A :- L @ l ] -> P Gamma A (L @ l) ->
    [ +n Gamma |- B :- s @ l ] -> P (+n Gamma) B (s @ l) ->
    P Gamma (Lolli A B L) (L @ l).
  Hypothesis ih_u_Var : forall Gamma x A,
    hasU Gamma x A -> P Gamma (Var x) A.
  Hypothesis ih_l_Var : forall Gamma x A,
    hasL Gamma x A -> P Gamma (Var x) A.
  Hypothesis ih_u_Lam : forall Gamma n A B s t l,
    pure Gamma ->
    [ Gamma |- Prod A B s :- Sort t l ] -> 
      P Gamma (Prod A B s) (Sort t l) ->
    [ A +{s} Gamma |- n :- B ] -> 
      P (A +{s} Gamma) n B ->
    P Gamma (Lam A n s) (Prod A B s).
  Hypothesis ih_l_Lam : forall Gamma n A B s t l,
    [ re Gamma |- Lolli A B s :- Sort t l ] -> 
      P (re Gamma) (Lolli A B s) (Sort t l) ->
    [ A +{s} Gamma |- n :- B ] ->
      P (A +{s} Gamma) n B ->
    P Gamma (Lam A n s) (Lolli A B s).
  Hypothesis ih_u_Prod_App : forall Gamma1 Gamma2 Gamma A B m n,
    pure Gamma2 ->
    [ Gamma1 |- m :- Prod A B U ] -> P Gamma1 m (Prod A B U) ->
    [ Gamma2 |- n :- A ] -> P Gamma2 n A ->
    merge Gamma1 Gamma2 Gamma ->
    P Gamma (App m n) B.[n/].
  Hypothesis ih_l_Prod_App : forall Gamma1 Gamma2 Gamma A B m n,
    [ Gamma1 |- m :- Prod A B L ] -> P Gamma1 m (Prod A B L) ->
    [ Gamma2 |- n :- A ] -> P Gamma2 n A ->
    merge Gamma1 Gamma2 Gamma ->
    P Gamma (App m n) B.[n/].
  Hypothesis ih_u_Lolli_App : forall Gamma1 Gamma2 Gamma A B m n,
    pure Gamma2 ->
    [ Gamma1 |- m :- Lolli A B U ] -> P Gamma1 m (Lolli A B U) ->
    [ Gamma2 |- n :- A ] -> P Gamma2 n A ->
    merge Gamma1 Gamma2 Gamma ->
    P Gamma (App m n) B.[n/].
  Hypothesis ih_l_Lolli_App : forall Gamma1 Gamma2 Gamma A B m n,
    [ Gamma1 |- m :- Lolli A B L ] -> P Gamma1 m (Lolli A B L) ->
    [ Gamma2 |- n :- A ] -> P Gamma2 n A ->
    merge Gamma1 Gamma2 Gamma ->
    P Gamma (App m n) B.[n/].
  Hypothesis ih_s_Ind : forall Gamma A s Cs l,
    arity s A ->
    List.Forall (constr 0 s) Cs ->
    pure Gamma ->
    [ Gamma |- A :- Sort U l ] -> P Gamma A (Sort U l) ->
    List.Forall (fun C => [ A +u Gamma |- C :- Sort U l ]) Cs ->
      List.Forall (fun C => P (A +u Gamma) C (Sort U l)) Cs ->
    P Gamma (Ind A Cs s) A.
  Hypothesis ih_s_Constr : forall Gamma A s i C Cs,
    let I := Ind A Cs s in
    iget i Cs C ->
    pure Gamma ->
    [ Gamma |- I :- A ] -> P Gamma I A ->
    P Gamma (Constr i I) C.[I/].
  Hypothesis ih_s_Case : forall Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms,
    let I := Ind A Cs s in
    arity s A ->
    merge Gamma1 Gamma2 Gamma ->
    [ Gamma1 |- m :- spine I ms ] -> P Gamma1 m (spine I ms) ->
    [ re Gamma2 |- Q :- arity1 s' A ] -> P (re Gamma2) Q (arity1 s' A) ->
    All2 (fun F C =>
      constr 0 s C /\
      [ Gamma2 |- F :- case I Q C ]) Fs Cs ->
    All2 (fun F C =>
      constr 0 s C /\
      P Gamma2 F (case I Q C)) Fs Cs ->
    P Gamma (Case m Q Fs) (spine Q ms).
  Hypothesis ih_s_DCase : forall Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms,
    let I := Ind A Cs U in
    arity s A ->
    pure Gamma1 ->
    merge Gamma1 Gamma2 Gamma ->
    [ Gamma1 |- m :- spine I ms ] -> P Gamma1 m (spine I ms) ->
    [ re Gamma2 |- Q :- arity2 s' I A ] -> P (re Gamma2) Q (arity2 s' I A) ->
    All2i (fun i F C =>
      constr 0 U C /\
      [ Gamma2 |- F :- (dcase I Q (Constr i I) C) ]) 0 Fs Cs ->
    All2i (fun i F C =>
      constr 0 U C /\
      P Gamma2 F (dcase I Q (Constr i I) C)) 0 Fs Cs ->
    P Gamma (DCase m Q Fs) (App (spine Q ms) m).
  Hypothesis ih_u_Fix : forall Gamma A m l,
    pure Gamma ->
    [ Gamma |- A :- Sort U l ] -> P Gamma A (Sort U l) ->
    [ A +u Gamma |- m :- A.[ren (+1)] ] -> P (A +u Gamma) m A.[ren (+1)] ->
    P Gamma (Fix A m) A.
  Hypothesis ih_s_Conv : forall Gamma A B m s l,
    A <: B ->
    [ re Gamma |- B :- Sort s l ] -> P (re Gamma) B (Sort s l) ->
    [ Gamma |- m :- A ] -> P Gamma m A ->
    P Gamma m B.

  Fixpoint has_type_nested_ind 
    Gamma m A (pf : [ Gamma |- m :- A ]) : P Gamma m A.
  Proof.
    case pf; intros.
    apply ih_u_Sort; eauto.
    eapply ih_u_Prod; eauto.
    eapply ih_l_Prod; eauto.
    eapply ih_u_Lolli; eauto.
    eapply ih_l_Lolli; eauto.
    apply ih_u_Var; eauto.
    apply ih_l_Var; eauto.
    eapply ih_u_Lam; eauto.
    eapply ih_l_Lam; eauto.
    eapply ih_u_Prod_App; eauto.
    eapply ih_l_Prod_App; eauto.
    eapply ih_u_Lolli_App; eauto.
    eapply ih_l_Lolli_App; eauto.
    eapply ih_s_Ind; eauto.
      apply (
        fix fold Cs 
          (pf : List.Forall 
            (fun C => [ A0 +u Gamma0 |- C :- Sort U l]) Cs) :
          List.Forall (fun C => P (A0 +u Gamma0) C (Sort U l)) Cs
        :=
          match pf with
          | List.Forall_nil => List.Forall_nil _
          | List.Forall_cons _ _ pfHd pfTl =>
            List.Forall_cons _ (has_type_nested_ind _ _ _ pfHd) (fold _ pfTl)
          end); eauto.
    apply ih_s_Constr; eauto.
    eapply ih_s_Case; eauto.
      apply (
        fix fold Fs Cs
          (pf : All2 (fun F C => 
            constr 0 s C /\
            [ Gamma2 |- F :- case I Q C ]) Fs Cs) :
          All2 (fun F C => 
            constr 0 s C /\
            P Gamma2 F (case I Q C)) Fs Cs
        :=
          match pf with
          | All2_nil => All2_nil _
          | All2_cons _ _ _ _ (conj h1 h2) tl =>
            All2_cons (conj h1 (has_type_nested_ind _ _ _ h2)) (fold _ _ tl)
          end); eauto.
    eapply ih_s_DCase; eauto.
      apply (
        fix fold n Fs Cs
          (pf : All2i (fun i F C => 
            constr 0 U C /\
            [ Gamma2 |- F :- dcase I Q (Constr i I) C ]) n Fs Cs) :
          All2i (fun i F C => 
            constr 0 U C /\
            P Gamma2 F (dcase I Q (Constr i I) C)) n Fs Cs
        :=
          match pf in 
            All2i _ n Fs Cs
          return
            All2i (fun i F C => 
              constr 0 U C /\
              P Gamma2 F (dcase I Q (Constr i I) C)) n Fs Cs
          with
          | All2i_nil _ => All2i_nil _ _
          | All2i_cons _ _ _ _ _ (conj h1 h2) pfTl =>
            All2i_cons (conj h1 (has_type_nested_ind _ _ _ h2)) (fold _ _ _ pfTl)
          end); eauto.
    eapply ih_u_Fix; eauto.
    eapply ih_s_Conv; eauto.
  Qed.
End has_type_nested_ind.

Lemma u_Prod_max Gamma A B s l1 l2 :
  pure Gamma ->
  [ Gamma |- A :- U @ l1 ] ->
  [ A +u Gamma |- B :- s @ l2 ] ->
  [ Gamma |- Prod A B U :- U @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Gamma |- A :- U @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ A +u Gamma |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: u_Prod; eauto.
Qed.

Lemma l_Prod_max Gamma A B s l1 l2 :
  pure Gamma ->
  [ Gamma |- A :- L @ l1 ] ->
  [ +n Gamma |- B :- s @ l2 ] ->
  [ Gamma |- Prod A B L :- U @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Gamma |- A :- L @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ +n Gamma |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: l_Prod; eauto.
Qed.

Lemma u_Lolli_max Gamma A B s l1 l2 :
  pure Gamma ->
  [ Gamma |- A :- U @ l1 ] ->
  [ A +u Gamma |- B :- s @ l2 ] ->
  [ Gamma |- Lolli A B U :- L @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Gamma |- A :- U @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ A +u Gamma |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: u_Lolli; eauto.
Qed.

Lemma l_Lolli_max Gamma A B s l1 l2 :
  pure Gamma ->
  [ Gamma |- A :- L @ l1 ] ->
  [ +n Gamma |- B :- s @ l2 ] ->
  [ Gamma |- Lolli A B L :- L @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Gamma |- A :- L @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ +n Gamma |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: l_Lolli; eauto.
Qed.
    
Inductive context_ok : context term -> Prop :=
| nil_ok :
  [ nil |- ]
| u_ok Gamma A l :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort U l ] ->
  [ A +u Gamma |- ]
| l_ok Gamma A l :
  [ Gamma |- ] ->
  [ re Gamma |- A :- Sort L l ] ->
  [ A +l Gamma |- ]
| n_ok Gamma :
  [ Gamma |- ] ->
  [ +n Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Lemma re_ok Gamma :
  [ Gamma |- ] ->
  [ re Gamma |- ].
Proof with eauto using context_ok.
  elim...
  move{Gamma}=> Gamma A l wf1 wf2 ty //=.
  apply: u_ok...
  rewrite <-re_re...
Qed.

Inductive agree_ren : (var -> var) ->
  context term -> context term -> Prop :=
| agree_ren_nil xi :
  agree_ren xi nil nil
| agree_ren_u Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m +u Gamma) (m.[ren xi] +u Gamma')
| agree_ren_l Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (m +l Gamma) (m.[ren xi] +l Gamma')
| agree_ren_n Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren (upren xi) (+n Gamma) (+n Gamma')
| agree_ren_wkU Gamma Gamma' xi m :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) Gamma (m +u Gamma')
| agree_ren_wkN Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
  agree_ren ((+1) ∘ xi) Gamma (+n Gamma').

Lemma agree_ren_refl Gamma : agree_ren id Gamma Gamma.
Proof.
  elim: Gamma.
  apply: agree_ren_nil.
  move=> a Gamma ag.
  destruct a.
  destruct p.
  destruct s.
  have h : (agree_ren id (t +u Gamma) (t +u Gamma)
    = agree_ren (upren id) (t +u Gamma) (t.[ren id] +u Gamma))
    by autosubst.
  rewrite h; constructor; eauto.
  have h : (agree_ren id (t +l Gamma) (t +l Gamma)
    = agree_ren (upren id) (t +l Gamma) (t.[ren id] +l Gamma))
    by autosubst.
  rewrite h; constructor; eauto.
  have h : (agree_ren id (+n Gamma) (+n Gamma)
    = agree_ren (upren id) (+n Gamma) (+n Gamma))
    by autosubst.
  rewrite h; constructor; eauto.
Qed.

Lemma agree_ren_pure Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' -> pure Gamma -> pure Gamma'.
Proof with eauto using pure.
  elim=>{Gamma Gamma' xi} //=...
  move=> Gamma Gamma' xi m ag ih pu.
    inv pu...
  move=> Gamma Gamma' xi m ag ih pu.
    inv pu.
  move=> Gamma Gamma' xi ag ih pu.
    inv pu...
Qed.

Lemma agree_ren_re_re Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' -> agree_ren xi (re Gamma) (re Gamma').
Proof. elim; eauto using agree_ren. Qed.

Lemma agree_ren_hasU Gamma Gamma' xi x A :
  agree_ren xi Gamma Gamma' ->
  hasU Gamma x A ->
  hasU Gamma' (xi x) A.[ren xi].
Proof with eauto.
  move=> ag. elim: ag x A=> {Gamma Gamma' xi}.
  move=> xi x A hs. inv hs.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_ren_pure...
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
  move=> Gamma Gamma' xi ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
Qed.

Lemma agree_ren_hasL Gamma Gamma' xi x A :
  agree_ren xi Gamma Gamma' ->
  hasL Gamma x A ->
  hasL Gamma' (xi x) A.[ren xi].
Proof with eauto.
  move=> ag. elim: ag x A=>{Gamma Gamma' xi}.
  move=> xi x A hs. inv hs.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
    replace (m0.[ren (+1)].[ren (upren xi)]) 
      with (m0.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_ren_pure...
  move=> Gamma Gamma' xi ag ih x A hs. inv hs.
    replace (m.[ren (+1)].[ren (upren xi)]) 
      with (m.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi m ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
  move=> Gamma Gamma' xi ag ih x A hs.
    replace (A.[ren ((+1) ∘ xi)])
      with (A.[ren xi].[ren (+1)]) by autosubst.
    constructor.
    exact: ih.
Qed.

Lemma merge_agree_ren_inv Gamma1 Gamma2 Gamma Gamma' xi :
  agree_ren xi Gamma Gamma' ->
    merge Gamma1 Gamma2 Gamma ->
    exists Gamma1' Gamma2',
      merge Gamma1' Gamma2' Gamma' /\
      agree_ren xi Gamma1 Gamma1' /\
      agree_ren xi Gamma2 Gamma2'.
Proof with eauto.
  move=> ag. elim: ag Gamma1 Gamma2=>{Gamma Gamma' xi}.
  move=> xi Gamma1 Gamma2 mg. inv mg.
    exists nil. exists nil. repeat constructor.
  move=> Gamma Gamma' xi m ag ih Gamma1 Gamma2 mg. inv mg.
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (m.[ren xi] +u Gamma1').
    exists (m.[ren xi] +u Gamma2').
    repeat constructor...
  move=> Gamma Gamma' xi m ag ih Gamma1 Gamma2 mg. inv mg.
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (m.[ren xi] +l Gamma1').
    exists (+n Gamma2').
      repeat constructor...
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (+n Gamma1').
    exists (m.[ren xi] +l Gamma2').
      repeat constructor...
  move=> Gamma Gamma' xi ag ih Gamma1 Gamma2 mg. inv mg.
    move: H2=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (+n Gamma1').
    exists (+n Gamma2').
    repeat constructor...
  move=> Gamma Gamma' xi m ag ih Gamma1 Gamma2 mg.
    move: mg=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (m +u Gamma1').
    exists (m +u Gamma2').
    repeat constructor...
  move=> Gamma Gamma' xi ag ih Gamma1 Gamma2 mg.
    move: mg=>/ih[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    exists (+n Gamma1').
    exists (+n Gamma2').
    repeat constructor...
Qed.

Lemma arity_ren s A xi : arity s A -> arity s A.[ren xi].
Proof with eauto using arity.
  move=> ar. elim: ar xi=>//=...
  move=> A' B ar ih xi.
    constructor.
    replace (up (ren xi)) with (ren (upren xi)) by autosubst.
    exact: ih.
Qed.

Definition n_ren (xi : var -> var) x :=
  xi x = x /\ 
    forall i, (~x = i -> ~xi i = x) /\ (~i = 0 -> ~xi i = 0).

Lemma n_ren0 xi : n_ren (upren xi) 0.
Proof.
  split; eauto.
  move=> i. elim: i xi=>//=.
Qed.

Lemma n_ren_up xi x :
  n_ren xi x -> n_ren (upren xi) x.+1.
Proof.
  move=>[e h]. split.
  asimpl; eauto.
  elim; asimpl; eauto.
  move=> n [ih1 ih2]. split; eauto.
  move=> neq. 
  have pf : ~x = n by eauto.
  move: (h n)=>[h1 h2].
  move: pf=>/h1; eauto.
Qed.

Lemma noccurs_ren x m xi :
  noccurs x m -> n_ren xi x -> noccurs x m.[ren xi].
Proof with eauto using noccurs, n_ren_up, and.
  move=> no. move: x m no xi.
  apply: noccurs_ind_nested=>//=...
  move=> x y neq xi [e h].
    move: (h y)=> {h} [h _].
    move: neq=> /h neq.
    constructor; eauto.
  move=> x A B s nA ihA nB ihB xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A B s nA ihA nB ihB xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A m s nA ihA nM ihM xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihM. exact: n_ren_up.
  move=> x A Cs s nA ihA nCs ihCs xi n.
    constructor.
    apply: ihA...
    elim: ihCs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'. apply n_ren_up...
    asimpl in ih...
  move=> x m Q Fs nM ihM nQ ihQ nFs ihFs xi n.
    constructor.
    apply: ihM...
    apply: ihQ...
    elim: ihFs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'...
    asimpl in ih...
  move=> x m Q Fs nM ihM nQ ihQ nFs ihFs xi n.
    constructor.
    apply: ihM...
    apply: ihQ...
    elim: ihFs=>//=.
    move=> x' l h' _ ih. constructor; asimpl.
    apply: h'...
    asimpl in ih...
  move=> x A m nA ihA nM ihM xi n.
    constructor.
    apply: ihA...
    asimpl. apply: ihM...
Qed.

Lemma noccurs_ren_Forall x ms xi :
  List.Forall (noccurs x) ms -> n_ren xi x ->
    List.Forall (noccurs x) ms..[ren xi].
Proof.
  move=> no. elim: no xi=>//={ms}.
  move=> m ms nM nMs ih xi n.
    constructor.
    apply: noccurs_ren; eauto.
    apply: ih; eauto.
Qed.

Lemma pos_ren x A xi :
  pos x A -> n_ren xi x -> pos x A.[ren xi].
Proof.
  move=> p. elim: p xi=>{x A}//=.
  move=> x ms no xi [e h].
    rewrite spine_subst=>//=.
    rewrite e. constructor. exact: noccurs_ren_Forall.
  move=> x A B s nA pB ihB xi n.
    constructor.
    exact: noccurs_ren.
    asimpl. apply: ihB. exact: n_ren_up.
  move=> x A B s nA pB ihB xi n.
    constructor.
    exact: noccurs_ren.
    asimpl. apply: ihB. exact: n_ren_up.
Qed.

Lemma active_ren i C xi :
  active i C -> n_ren xi i -> active i C.[ren xi].
Proof.
  move=> c. elim: c xi=>{i C}//=.
  move=> x ms no xi [e h].
    rewrite spine_subst; asimpl.
    rewrite e.
    apply: active_X.
    elim: no=>//=.
    move{ms}=> m ms nM nMs ihMs.
      constructor; asimpl.
      apply: noccurs_ren; eauto; constructor; eauto.
      exact: ihMs.
  move=> x A B s pA c ih nB xi n.
    apply: active_Pos.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. exact: n_ren0.
  move=> x A B s nA c ih xi n.
    apply: active_Lolli.
    apply: noccurs_ren; eauto.
    asimpl. apply: ih. exact: n_ren_up.
Qed.  

Lemma constr_ren i s C xi :
  constr i s C -> n_ren xi i -> constr i s C.[ren xi].
Proof.
  move=> c. elim: c xi=>{i s C}.
  move=> x s ms no xi [e h].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no=>//=.
    move{ms}=> m ms nM nMs ihMs.
      constructor.
      apply: noccurs_ren; eauto; constructor; eauto.
      apply: ihMs.
  move=> x A B pA c ih nB xi n=>//=.
    apply: constr_UPos.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. apply n_ren0.
  move=> x A B nA cB ih xi n=>//=.
    apply: constr_UProd.
    apply: noccurs_ren; eauto.
    asimpl. apply: ih. exact: n_ren_up.
  move=> x A B pA cB ih no xi n=>//=.
    apply: constr_LPos1.
    exact: pos_ren.
    asimpl. apply: ih. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. apply n_ren0.
  move=> x A B pA c nB xi n=>//=.
    apply: constr_LPos2.
    exact: pos_ren.
    asimpl. apply: active_ren; eauto. exact: n_ren_up.
    asimpl. apply: noccurs_ren; eauto. exact: n_ren0.
  move=> x A B nA c ih xi n=>//=.
    apply: constr_LProd1.
    exact: noccurs_ren.
    asimpl. apply: ih. exact: n_ren_up.
  move=> x A B nA c xi n=>//=.
    apply: constr_LProd2.
    exact: noccurs_ren.
    asimpl. apply: active_ren; eauto. exact: n_ren_up.
Qed.

Lemma drespine_respine I :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall Q, respine Q I = Q).
Proof.
  elim: I=>//=.
  move=> A _ B _ s h Q.
    move: (h Q (Var 0))=>//=.
  move=> A _ B _ s h Q.
    move: (h (Lam Q Q s) (Var 0))=>//=.
  move=> m _ n _ h Q.
    move: (h (Lam Q Q U) (Var 0))=>//=.
Qed.

Lemma respine_ren1 (I : var -> term) :
  (forall i Q, respine Q (I i) = Q) ->
  (forall i Q, respine Q (I i).[ren (+1)] = Q).
Proof.
  move=> h i.
  move e:(I i)=> n.
  elim: n e h=>//=.
  move=> A _ B _ s e h Q.
    move: (h i (Var 0)).
    by rewrite e=>//=.
  move=> A _ B _ s e h Q.
    move: (h i (Var 0)).
    by rewrite e=>//=.
  move=> m _ n _ e h Q.
    move: (h i (Var 0)).
    by rewrite e=>//=.
Qed.

Lemma drespine_ren1 (I : var -> term) :
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (forall i c Q, drespine Q c (I i).[ren (+1)] = App Q c).
Proof.
  move=> h i.
  move e:(I i)=> n.
  elim: n e h=>//=.
  move=> A _ B _ s e h c Q.
    move: (h i c (Var 0)).
    by rewrite e=>//=.
  move=> A _ B _ s e h c Q.
    move: (h i c (Var 0)).
    by rewrite e=>//=.
  move=> m _ n _ e h c Q.
    move: (h i c (Var 0)).
    by rewrite e=>//=.
Qed.

Lemma respine_up I :
  (forall i Q, respine Q (I i) = Q) ->
  (forall i Q, respine Q (up I i) = Q).
Proof.
  move=> h i.
  elim: i I h=>//=.
  move=> i ih I h Q; asimpl.
  by apply respine_ren1.
Qed.

Lemma drespine_up I :
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (forall i c Q, drespine Q c (up I i) = App Q c).
Proof.
  move=> h i.
  elim: i I h=>//=.
  move=> i ih I h c Q; asimpl.
  by apply drespine_ren1.
Qed.

Lemma arity1_ren s s' A xi : 
  arity s A -> (arity1 s' A).[ren xi] = arity1 s' A.[ren xi].
Proof.
  move=> ar. elim: ar xi s'=>{A}//=.
  move=> A B ar ih xi s'; asimpl.
  rewrite ih; eauto.
Qed.

Lemma arity2_ren s s' I A xi : 
  arity s A -> (arity2 s' I A).[ren xi] = arity2 s' I.[ren xi] A.[ren xi].
Proof.
  move=> ar. elim: ar I xi s'=>{A}//=.
  move=> A B ar ih I xi s'; asimpl.
  rewrite ih; asimpl; eauto.
Qed.

Lemma respine_I_ren Q I xi :
  (forall Q, respine Q I = Q) ->
  Q.[ren xi] = respine Q.[ren xi] I.[ren xi].
Proof.
  elim: I xi Q=>//=.
  move=> A _ B _ s xi Q h.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s xi Q h.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi Q h.
    move: (h (Var 0))=>//=.
Qed.

Lemma drespine_I_ren Q c I xi :
  (forall Q, drespine Q c I = App Q c) ->
  App Q.[ren xi] c.[ren xi] = drespine Q.[ren xi] c.[ren xi] I.[ren xi].
Proof.
  elim: I xi c Q=>//=.
  move=> A _ B _ s xi c Q h.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s xi c Q h.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi c Q h.
    move: (h (Var 0))=>//=.
Qed.

Lemma respine_spine'_I_ren Q I ms xi :
  (forall Q, respine Q I = Q) ->
  (respine Q (spine' I ms)).[ren xi] =
    respine Q.[ren xi] (spine' I ms).[ren xi].
Proof.
  elim: ms Q I xi=>//=.
  move=> Q I xi h.
    rewrite h.
    by apply respine_I_ren.
  move=> m ms ih Q I xi h.
    rewrite ih; eauto.
Qed.

Lemma drespine_spine'_I_ren Q c I ms xi :
  (forall Q c, drespine Q c I = App Q c) ->
  (drespine Q c (spine' I ms)).[ren xi] =
    drespine Q.[ren xi] c.[ren xi] (spine' I ms).[ren xi].
Proof.
  elim: ms Q c I xi=>//=.
  move=> Q c I xi h.
    rewrite h.
    by apply drespine_I_ren.
  move=> m ms ih Q c I xi h.
    repeat f_equal.
    apply respine_spine'_I_ren.
    by apply drespine_respine.
Qed.

Lemma respine_spine_I_ren Q I ms xi :
  (forall Q, respine Q I = Q) ->
  (respine Q (spine I ms)).[ren xi] =
    respine Q.[ren xi] (spine I ms).[ren xi].
Proof.
  move=> h.
  rewrite spine_spine'_rev.
  by rewrite respine_spine'_I_ren.
Qed.

Lemma drespine_spine_I_ren Q c I ms xi :
  (forall Q c, drespine Q c I = App Q c) ->
  (drespine Q c (spine I ms)).[ren xi] =
    drespine Q.[ren xi] c.[ren xi] (spine I ms).[ren xi].
Proof.
  move=> h.
  rewrite spine_spine'_rev.
  by rewrite drespine_spine'_I_ren.
Qed.

Lemma active_respine_ren n (Q C : term) I (xi : var -> var) :
  active n C ->
  (forall i Q, respine Q (I i) = Q) ->
  (respine Q C.[I]).[ren xi] = 
    respine Q.[ren xi] C.[I].[ren xi].
Proof.
  move=> c; unfold case.
  elim: c Q I xi; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
Qed.

Lemma active_drespine_ren n (Q c C : term) I (xi : var -> var) :
  active n C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (drespine Q c C.[I]).[ren xi] = 
    drespine Q.[ren xi] c.[ren xi] C.[I].[ren xi].
Proof.
  move=> a; unfold case.
  elim: a c Q I xi; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. repeat f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    apply: respine_up=> i.
    by apply: drespine_respine.
  - asimpl. repeat f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    apply: respine_up=> i.
    by apply: drespine_respine.
Qed.

Lemma constr_respine_ren n s (Q C : term) I (xi : var -> var) :
  constr n s C ->
  (forall i Q, respine Q (I i) = Q) ->
  (respine Q C.[I]).[ren xi] = 
    respine Q.[ren xi] C.[I].[ren xi].
Proof.
  move=> c; unfold case.
  elim: c Q I xi; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply respine_up.
  - asimpl. f_equal.
    erewrite active_respine_ren; asimpl; eauto.
    by apply respine_up.
Qed.

Lemma constr_drespine_ren n s (Q c C : term) I (xi : var -> var) :
  constr n s C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (drespine Q c C.[I]).[ren xi] = 
    drespine Q.[ren xi] c.[ren xi] C.[I].[ren xi].
Proof.
  move=> cn; unfold case.
  elim: cn Q c I xi; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_ren.
    rewrite! spine_subst; asimpl; eauto.
    destruct x; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    erewrite active_drespine_ren; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    by apply drespine_up.
  - asimpl. f_equal.
    erewrite active_drespine_ren; asimpl; eauto.
    by apply drespine_up.
Qed.

Lemma All2_case_ren Gamma Gamma' s A Q Fs Cs Cs' xi :
  All2 (fun F C =>
    constr 0 s C /\
    forall Gamma' xi, agree_ren xi Gamma Gamma' ->
      [ Gamma' |- F.[ren xi] :- (case (Ind A Cs' s) Q C).[ren xi] ])
    Fs Cs ->
  agree_ren xi Gamma Gamma' ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Gamma' |- F :- case (Ind A.[ren xi] Cs'..[up (ren xi)] s) Q.[ren xi] C])
    Fs..[ren xi] Cs..[up (ren xi)].
Proof.
  elim: Fs Gamma Gamma' s A Q Cs xi.
  move=> Gamma Gamma' s A Q Cs xi h. inv h=> *.
    constructor.
  move=> F Fs ih Gamma Gamma' s A Q Cs xi h ag.
  destruct Cs; inv h. inv H2; asimpl.
  constructor. split.
  - apply: constr_ren; eauto.
    apply: n_ren0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold case in H0.
    erewrite constr_respine_ren in H0; eauto.
    asimpl in H0.
    by unfold case; asimpl.
    move=> i Q'.
    destruct i; asimpl; eauto.
  - replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih; eauto.
Qed.

Lemma All2i_case_ren Gamma Gamma' n s A Q Fs Cs Cs' xi :
  All2i (fun i F C =>
    let I := Ind A Cs' s in
    constr 0 s C /\
    forall Gamma' xi, agree_ren xi Gamma Gamma' ->
      [ Gamma' |- F.[ren xi] :- (dcase I Q (Constr i I) C).[ren xi] ])
    n Fs Cs ->
  agree_ren xi Gamma Gamma' ->
  All2i (fun i F C =>
    let I := Ind A.[ren xi] Cs'..[up (ren xi)] s in
    constr 0 s C /\
    [ Gamma' |- F :- dcase I Q.[ren xi] (Constr i I) C])
    n Fs..[ren xi] Cs..[up (ren xi)].
Proof.
  elim: Fs Gamma Gamma' n s A Q Cs xi.
  move=> Gamma Gamma' n s A Q Cs xi h. inv h=> *.
    constructor.
  move=> F Fs ih Gamma Gamma' n s A Q Cs xi h ag.
  destruct Cs; inv h. inv H3; asimpl.
  constructor. split.
  - apply: constr_ren; eauto.
    apply: n_ren0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold dcase in H0.
    erewrite constr_drespine_ren in H0; eauto.
    asimpl in H0.
    by unfold dcase; asimpl.
    move=> i Q'.
    destruct i; asimpl; eauto.
  - replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih; eauto.
Qed.

Lemma rename_ok Gamma Gamma' m A xi :
  [ Gamma |- m :- A ] ->
  agree_ren xi Gamma Gamma' ->
  [ Gamma' |- m.[ren xi] :- A.[ren xi] ].
Proof with eauto using agree_ren, agree_ren_pure, agree_ren_re_re.
  move=> ty.
  move: Gamma m A ty Gamma' xi.
  apply: has_type_nested_ind=> //=.
  move=> Gamma s l pu Gamma' xi ag.
    apply: u_Sort...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: u_Prod...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: l_Prod...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: u_Lolli...
  move=> Gamma A B s l pu tyA ihA tyB ihB Gamma' xi ag; asimpl.
    apply: l_Lolli...
  move=> Gamma x A hs Gamma' xi ag //=.
    apply: u_Var.
    apply: agree_ren_hasU...
  move=> Gamma x A hs Gamma' xi ag //=.
    apply: l_Var.
    apply: agree_ren_hasL...
  move=> Gamma n A B s t l pu ty1 ih1 ty2 ih2 Gamma' xi ag.
    apply: u_Lam...
    asimpl. apply: ih2. destruct s; constructor...
  move=> Gamma n A B s t l ty1 ih1 ty2 ih2 Gamma' xi ag.
    apply: l_Lam.
    apply: ih1. apply: agree_ren_re_re...
    asimpl. apply: ih2. destruct s; constructor...
  move=> Gamma1 Gamma2 Gamma A B m n pu ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    move: (agree_ren_pure ag2 pu)=> {} pu.
    apply: u_Prod_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma1 Gamma2 Gamma A B m n ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    apply: l_Prod_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma1 Gamma2 Gamma A B m n pu ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    move: (agree_ren_pure ag2 pu)=> {} pu.
    apply: u_Lolli_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma1 Gamma2 Gamma A B m n ty1 ih1 ty2 ih2 mg Gamma' xi ag.
    asimpl.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    replace (B.[n.[ren xi] .: ren xi]) 
      with (B.[ren (upren xi)].[n.[ren xi]/]) by autosubst.
    apply: l_Lolli_App...
    replace (ren (upren xi)) with (up (ren xi)) by autosubst.
    apply: ih1...
  move=> Gamma A s Cs l ar cnstr pu ty1 ih1 ty2 ih2 Gamma' xi ag.
    apply: s_Ind...
    exact: arity_ren.
    move=>{ag}. elim: cnstr xi=>//=...
      move=> m ms c hMs ihMs xi; asimpl.
      constructor. 
      apply: constr_ren... apply: n_ren0.
      move: (ihMs xi)=> {} ihMs.
      asimpl in ihMs. exact: ihMs.
    elim: ih2=>//=.
      move=> m ms ihM hMs ihMs; asimpl.
      constructor. 
      asimpl. apply: ihM...
      asimpl in ihMs. exact: ihMs.
  move=> Gamma A s i C Cs ig pu ty ih Gamma' xi ag.
    replace (C.[Ind A Cs s/].[ren xi]) 
      with (C.[up (ren xi)]).[Ind A.[ren xi] Cs..[up (ren xi)] s/]
        by autosubst.
    apply: s_Constr...
    apply: iget_subst...
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms ar mg 
    tyM ihM tyQ ihQ ty ih Gamma' xi ag.
    rewrite spine_subst.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    move: (arity_ren xi ar)=> ar'.
    move: (agree_ren_re_re ag2)=> rag2.
    move: (ihM _ _ ag1)=> {} ihM. rewrite spine_subst in ihM.
    move: (ihQ _ _ rag2)=> {} ihQ.
    move: (arity1_ren s' xi ar)=> e. rewrite e in ihQ.
    apply: s_Case...
    apply: All2_case_ren...
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms ar p mg
    tyM ihM tyQ ihQ ty ih Gamma' xi ag.
    rewrite spine_subst.
    move: (merge_agree_ren_inv ag mg)=>[Gamma1'[Gamma2'[mg'[ag1 ag2]]]].
    move: (arity_ren xi ar)=> ar'.
    move: (agree_ren_re_re ag2)=> rag2.
    move: (ihM _ _ ag1)=> {} ihM. rewrite spine_subst in ihM.
    move: (ihQ _ _ rag2)=> {} ihQ.
    move: (arity2_ren s' (Ind A Cs U) xi ar)=> e. rewrite e in ihQ.
    move: (agree_ren_pure ag1 p)=>{}p.
    apply: s_DCase...
    apply: All2i_case_ren...
  move=> Gamma A m l p tyA ihA tyM ihM Gamma' xi ag.
    econstructor...
    have ag' : agree_ren (upren xi) (A +u Gamma) (A.[ren xi] +u Gamma').
      by constructor.
    move: (ihM _ _ ag'); asimpl=>//.
  move=> Gamma A B m s l sub tyB ihB tyM ihM Gamma' xi ag.
    apply: s_Conv.
    apply: sub_ren.
    apply: sub.
    apply: ihB.
    by apply: agree_ren_re_re.
    by apply: ihM.
Qed.

Lemma hasU_ok Gamma x A :
  [ Gamma |- ] ->
  hasU Gamma x A ->
  exists l, [ re Gamma |- A :- Sort U l ].
Proof.
  move=> wf. elim: wf x A.
  move=> x A h. inv h.
  move=> Gamma' A l wf ih tyA x A' h. inv h=>//=.
    exists l.
    replace (Sort U l) with (Sort U l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
    move: (ih _ _ H3)=>{ih}[l' tyM].
    exists l'.
    replace (Sort U l') with (Sort U l').[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
  move=> Gamma' A l wf ih tyA x A' h. inv h.
  move=> Gamma' wf ih x A h. inv h=>//=.
    move: (ih _ _ H0)=>{ih}[l tyM].
    exists l.
    replace (Sort U l) with (Sort U l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
Qed.

Lemma hasL_ok Gamma x A :
  [ Gamma |- ] ->
  hasL Gamma x A ->
  exists l, [ re Gamma |- A :- Sort L l ].
Proof.
  move=> wf. elim: wf x A.
  move=> x A h. inv h.
  move=> Gamma' A l wf ih tyA x A' h=>//=. inv h.
    move: (ih _ _ H3)=>{ih}[l' tyM].
    exists l'.
    replace (Sort L l') with (Sort L l').[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkU.
    apply: agree_ren_refl.
  move=> Gamma' A l wf ih tyA x A' h=>//=. inv h.
    exists l.
    replace (Sort L l) with (Sort L l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
  move=> Gamma' wf ih x A h=>//=. inv h.
    move: (ih _ _ H0)=>{ih}[l tyM].
    exists l.
    replace (Sort L l) with (Sort L l).[ren (+1)] by autosubst.
    apply: rename_ok; eauto.
    apply: agree_ren_wkN.
    apply: agree_ren_refl.
Qed.

Lemma weakeningU Gamma m A B :
  [ Gamma |- m :- A ] ->
  [ B +u Gamma |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> tyM.
  apply: rename_ok; eauto.
  apply: agree_ren_wkU.
  apply: agree_ren_refl.
Qed.

Lemma weakeningN Gamma m A :
  [ Gamma |- m :- A ] ->
  [ +n Gamma |- m.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> tyM.
  apply: rename_ok; eauto.
  apply: agree_ren_wkN.
  apply: agree_ren_refl.
Qed.

Lemma eweakeningU Gamma m m' A A' B :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A ] -> 
  [ B +u Gamma |- m' :- A' ].
Proof.
  move=>->-> h.  
  apply: weakeningU; eauto.
Qed.

Lemma eweakeningN Gamma m m' A A' :
  m' = m.[ren (+1)] -> 
  A' = A.[ren (+1)] ->
  [ Gamma |- m :- A ] -> 
  [ +n Gamma |-m' :- A' ].
Proof.
  move=>->-> h.
  apply: weakeningN; eauto.
Qed.

Reserved Notation "[ Delta |- sigma -| Gamma ]".

Inductive agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil sigma :
  [ nil |- sigma -| nil ]
| agree_subst_u Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] +u Delta |- up sigma -| A +u Gamma ]
| agree_subst_l Delta sigma Gamma A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] +l Delta |- up sigma -| A +l Gamma ]
| agree_subst_n Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ +n Delta |- up sigma -| +n Gamma ]
| agree_subst_wkU Delta sigma Gamma n A :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- n :- A.[sigma] ] ->
  [ Delta |- n .: sigma -| A +u Gamma ]
| agree_subst_wkL Delta1 Delta2 Delta sigma Gamma n A :
  merge Delta1 Delta2 Delta ->
  [ Delta1 |- sigma -| Gamma ] ->
  [ Delta2 |- n :- A.[sigma] ] ->
  [ Delta |- n .: sigma -| A +l Gamma ]
| agree_subst_wkN Delta sigma Gamma n :
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- n .: sigma -| +n Gamma ]
| agree_subst_convU Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[sigma] :- Sort U l ] ->
  [ Delta |- sigma -| A +u Gamma ] ->
  [ Delta |- sigma -| B +u Gamma ]
| agree_subst_convL Delta sigma Gamma A B l :
  A <: B ->
  [ re Delta |- B.[ren (+1)].[sigma] :- Sort L l ] ->
  [ re Gamma |- B :- Sort L l ] ->
  [ Delta |- sigma -| A +l Gamma ] ->
  [ Delta |- sigma -| B +l Gamma ]
where "[ Delta |- sigma -| Gamma ]" := (agree_subst Delta sigma Gamma).

Lemma agree_subst_pure Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] -> pure Gamma -> pure Delta.
Proof with eauto using pure.
  elim=>//=...
  move=> Delta' sigma' Gamma' A ag h p. inv p...
  move=> Delta' sigma' Gamma' A ag h p. inv p.
  move=> Delta' sigma' Gamma' ag h p. inv p...
  move=> Delta' sigma' Gamma' n A ag1 h ag2 p. inv p...
  move=> Delta1 Delta2 Delta' sigma' Gamma' n A mg ag1 h ag2 p. inv p.
  move=> Delta' sigma' Gamma' _ ag h p. inv p...
  move=> Delta' sigma' Gamma' A B l sb ag1 ag2 h p. inv p...
  move=> Delta' sigma' Gamma' A B l sb ty1 ty2 ag h p. inv p.
Qed.

Lemma agree_subst_refl Gamma : [ Gamma |- ids -| Gamma ].
Proof with eauto using agree_subst.
  elim: Gamma...
  move=> a Gamma ag.
  destruct a.
  destruct p.
  destruct s.
  replace [ t +u Gamma |- ids -| t +u Gamma ]
    with [ t.[ids] +u Gamma |- up ids -| t +u Gamma ]
    by autosubst...
  replace [ t +l Gamma |- ids -| t +l Gamma ]
    with [ t.[ids] +l Gamma |- up ids -| t +l Gamma ]
    by autosubst...
  replace ids with (up ids) by autosubst...
Qed.

Lemma agree_subst_hasU Delta sigma Gamma x A :
  [ Delta |- sigma -| Gamma ] ->
  hasU Gamma x A ->
  [ Delta |- sigma x :- A.[sigma] ].
Proof.
  move=> ag. elim: ag x A=>{sigma Delta Gamma}.
  move=> sigma x A h. inv h.
  move=> Delta sigma Gamma A ag ih x A' h. inv h; asimpl.
    apply: u_Var.
    replace (A.[sigma >> ren (+1)])
      with (A.[sigma].[ren (+1)]) by autosubst.
    constructor.
    apply: agree_subst_pure; eauto.
    apply: eweakeningU; eauto. autosubst.
  move=> Delta sigma Gamma A ag ih x A' h. inv h.
  move=> Delta sigma Gamma Ag ih x A h. inv h.
    apply: eweakeningN; eauto; autosubst.
  move=> Delta sigma Gamma n A ag ih ty x A' h. 
    inv h; asimpl; eauto.
    have p := agree_subst_pure ag H3.
    by rewrite (pure_re p).
  move=> Delta1 Delta2 Delta sigma Gamma n A mg ag ih ty x A' h. 
    inv h.
  move=> Delta sigma Gamma n ag ih x A h. inv h; asimpl; eauto.
  move=> Delta sigma Gamma A B l sb ty ag ih x A' h. inv h.
    have h' : hasU (A +u Gamma) 0 A.[ren (+1)].
      constructor; eauto.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub_ren; eauto.
    apply: ty.
    apply: ih; eauto.
    apply: ih.
    constructor; eauto.
  move=> Delta sigma Gamma A B l sb t1 ty2 ag ih x A' h.
    inv h.
Qed.

Lemma agree_subst_hasL Delta sigma Gamma x A :
  [ Delta |- sigma -| Gamma ] ->
  hasL Gamma x A ->
  [ Delta |- sigma x :- A.[sigma] ].
Proof.
  move=> ag. elim: ag x A=>{Delta sigma Gamma}.
  move=> sigma x A h. inv h.
  move=> Delta sigma Gamma A ag ih x A' h. inv h.
    apply: eweakeningU; eauto; autosubst.
  move=> Delta sigma Gamma A ag ih x A' h. inv h; asimpl.  
    replace (A.[sigma >> ren (+1)])
      with (A.[sigma].[ren (+1)]) by autosubst.
    apply: l_Var.
    constructor.
    apply: agree_subst_pure; eauto.
  move=> Delta sigma Gamma ag ih x A h. inv h.
    apply: eweakeningN; eauto; autosubst.
  move=> Delta sigma Gamma n A ag ih ty x A' h. 
    inv h; asimpl; eauto.
  move=> Delta1 Delta2 Delta sigma Gamma n A mg ag ih ty x A' h.
    inv h; asimpl.
    have p := agree_subst_pure ag H3.
    rewrite (merge_pure1 mg p); eauto.
  move=> Delta sigma Gamma n ag ih x A h. inv h; asimpl; eauto.
  move=> Delta sigma Gamma A B l sb ty ag ih x A' h. inv h.
    apply: ih.
    constructor; eauto.
  move=> Delta sigma Gamma A B l sb ty1 ty2 ag ih x A' h. inv h.
    have h' : hasL (A +l Gamma) 0 A.[ren (+1)].
      constructor; eauto.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub_ren; eauto.
    apply: ty1.
    apply: ih; eauto.
Qed.

Lemma agree_subst_re_re Delta sigma Gamma :
  [ Delta |- sigma -| Gamma ] ->
  [ re Delta |- sigma -| re Gamma ].
Proof with eauto using agree_subst.
  move=> ag. elim: ag=>//={Delta sigma Gamma}...
  move=> Delta sigma Gamma n A ag1 ag2 ty.
    constructor...
    rewrite <- re_re...
  move=> Delta1 Delta2 Delta sigma Gamma n A mg ag1 ag2 ty.
    constructor...
    move: (merge_re_re mg)=>[<-_]...
  move=> Delta sigma Gamma A B l sb ty ag1 ag2.
    apply: agree_subst_convU...
    rewrite <- re_re...
Qed.

Lemma merge_agree_subst_inv Delta sigma Gamma1 Gamma2 Gamma :
  [ Delta |- sigma -| Gamma ] ->
  merge Gamma1 Gamma2 Gamma ->
  exists Delta1 Delta2,
    merge Delta1 Delta2 Delta /\
    [ Delta1 |- sigma -| Gamma1 ] /\
    [ Delta2 |- sigma -| Gamma2 ].
Proof.
  move=> ag. elim: ag Gamma1 Gamma2=>{Delta sigma Gamma}.
  move=> sigma Gamma1 Gamma2 mg. inv mg.
    exists nil. exists nil. repeat constructor; eauto.
  move=> Delta sigma Gamma A ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists (A.[sigma] +u Delta1).
    exists (A.[sigma] +u Delta2).
    repeat constructor; eauto.
  move=> Delta sigma Gamma A ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists (A.[sigma] +l Delta1).
      exists (+n Delta2).
      repeat constructor; eauto.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists (+n Delta1).
      exists (A.[sigma] +l Delta2).
      repeat constructor; eauto.
  move=> Delta sigma Gamma ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists (+n Delta1).
    exists (+n Delta2).
    repeat constructor; eauto.
  move=> Delta sigma Gamma n A ag ih ty Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists Delta1. 
    exists Delta2.
    move: (merge_re_re mg')=>[e1 e2]. 
    repeat constructor; eauto.
    move: e1=>->; eauto.
    move: e2=>->; eauto.
  move=> Delta1 Delta2 Delta sigma Gamma n A mg1 ag ih ty
    Gamma1 Gamma2 mg2. inv mg2.
    move: (ih _ _ H2)=> {H2}[Delta1'[Delta2'[mg'[ag1 ag2]]]].
      move: (merge_split1 mg1 mg')=>[Delta'[mg1' mg2']].
      exists Delta'. 
      exists Delta2'.
      repeat constructor; eauto.
      apply: agree_subst_wkL; eauto.
    move: (ih _ _ H2)=> {H2}[Delta1'[Delta2'[mg'[ag1 ag2]]]].
      move: (merge_split2 mg1 mg')=>[Delta'[mg1' mg2']].
      exists Delta1'.
      exists Delta'.
      repeat constructor; eauto.
      apply: agree_subst_wkL; eauto.
  move=> Delta sigma Gamma n ag ih Gamma1 Gamma2 mg. inv mg.
    move: (ih _ _ H2)=> {H2}[Delta1[Delta2[mg'[ag1 ag2]]]].
    exists Delta1.
    exists Delta2.
    repeat constructor; eauto.
  move=> Delta sigma Gamma A B l sb ty ag ih Gamma1 Gamma2 mg.
    inv mg.
    have mg : merge (A +u Gamma0) (A +u Gamma3) (A +u Gamma).
      constructor; eauto.
    move: (ih _ _ mg)=>{mg}[Delta1[Delta2[mg[ag1 ag2]]]].
    exists Delta1.
    exists Delta2.
    move: (merge_re_re mg)=>[e1 e2].
    repeat constructor; eauto.
    apply: agree_subst_convU; eauto.
    rewrite e1; eauto.
    apply: agree_subst_convU; eauto.
    rewrite e2; eauto.
  move=> Delta sigma Gamma A B l sb ty1 ty2 ag ih Gamma1 Gamma2 mg.
    inv mg.
    have mg' : merge (A +l Gamma0) (+n Gamma3) (A +l Gamma).
      constructor; eauto.
      move: (ih _ _ mg')=>{mg'}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists Delta1.
      exists Delta2.
      move: (merge_re_re H2)=>[eG1 eG2].
      move: (merge_re_re mg')=>[eD1 eD2].
      repeat constructor; eauto.
      apply: agree_subst_convL; eauto.
      move: eD1=>->; eauto.
      move: eG1=>->; eauto.
    have mg' : merge (+n Gamma0) (A +l Gamma3) (A +l Gamma).
      constructor; eauto.
      move: (ih _ _ mg')=>{mg'}[Delta1[Delta2[mg'[ag1 ag2]]]].
      exists Delta1.
      exists Delta2.
      move: (merge_re_re H2)=>[eG1 eG2].
      move: (merge_re_re mg')=>[eD1 eD2].
      repeat constructor; eauto.
      apply: agree_subst_convL; eauto.
      move: eD2=>->; eauto.
      move: eG2=>->; eauto.
Qed.

Lemma arity_subst s A sigma :
  arity s A -> arity s A.[sigma].
Proof with eauto using arity.
  move=> ar. elim: ar sigma...
Qed.

Definition n_subst sigma x := 
  (forall i, ~x = i -> noccurs x (sigma i)) /\ sigma x = Var x.

Lemma noccurs_ren0 x m xi :
  (forall i, ~xi i = x) -> noccurs x m.[ren xi].
Proof with eauto using noccurs, List.Forall.
  move: m x xi. apply: term_ind_nested...
  move=> A B s ihA ihB x xi h; asimpl.
    constructor...
    apply: ihB=> i.
    destruct i; asimpl; eauto.
  move=> A B s ihA ihB x xi h; asimpl.
    constructor...
    apply: ihB=> i.
    destruct i; asimpl; eauto.
  move=> A m s ihA ihM x xi h; asimpl.
    constructor...
    apply: ihM=> i.
    destruct i; asimpl; eauto.
  move=> A Cs s ihA ihCs x xi h; asimpl.
    constructor...
    elim: ihCs...
    move=> C Cs' hd tl ih.
    constructor...
    apply: hd=> i.
    destruct i; asimpl; eauto.
  move=> m Q Fs ihM ihQ ihFs x xi h; asimpl.
    constructor...
    elim: ihFs...
  move=> m Q Fs ihM ihQ ihFs x xi h; asimpl.
    constructor...
    elim: ihFs...
  move=> A m ihA ihM x xi h; asimpl.
    constructor...
    apply: ihM=> i.
    destruct i; asimpl; eauto.
Qed.

Lemma n_subst0 sigma : n_subst (up sigma) 0.
Proof.
  split; eauto.
  move=> i. elim: i sigma=>//=.
  move=> i _ sigma _; asimpl.
  apply: noccurs_ren0; eauto.
Qed.

Lemma noccurs_up x m xi :
  noccurs x m -> 
    (forall i, ~x = i -> ~xi x = xi i) -> 
    noccurs (xi x) m.[ren xi].
Proof with eauto using noccurs.
  move=> no. move: x m no xi.
  apply: noccurs_ind_nested=>//=... 
  move=> x A B s noA ihA noB ihB xi h.
    constructor; asimpl; eauto.
    apply: ihB=> i. 
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A B s noA ihA noB ihB xi h.
    constructor; asimpl; eauto.
    apply: ihB=> i. 
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A m s noA ihA noM ihM xi h.
    constructor; asimpl; eauto.
    apply: ihM=> i.
    destruct i; asimpl; eauto.
    move=> n.
    have /h neq : ~x = i by eauto.
    eauto.
  move=> x A Cs s noA ihA noCs ihCs xi h.
    constructor; asimpl; eauto.
    elim: ihCs.
    asimpl; constructor.
    move=> C Cs' hd tl ih; asimpl.
    constructor; eauto.
    apply: hd=> i neq.
    destruct i; asimpl; eauto.
    have /h neq' : ~x = i by eauto.
    eauto.
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs xi h.
    constructor; asimpl; eauto.
    elim: ihFs.
    asimpl; constructor.
    move=> F Fs' hd tl ih; asimpl.
    constructor; eauto.
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs xi h.
    constructor; asimpl; eauto.
    elim: ihFs.
    asimpl; constructor.
    move=> F Fs' hd tl ih; asimpl.
    constructor; eauto.
  move=> x A m noA ihA noM ihM xi h.
    constructor; asimpl; eauto.
    apply: ihM=> i neq.
    destruct i; asimpl; eauto.
    have /h neq' : ~x = i by eauto.
    eauto.
Qed.

Lemma n_subst_up sigma x :
  n_subst sigma x -> n_subst (up sigma) x.+1.
Proof.
  move=>[h e]. split; asimpl.
  elim; asimpl.
  constructor; eauto.
  move=> n h' neq.
  have pf : ~x = n by eauto.
  move: (h _ pf)=>{}h.
  apply: noccurs_up; eauto.
  rewrite e. autosubst.
Qed.

Lemma noccurs_subst sigma m x :
  noccurs x m -> n_subst sigma x -> noccurs x m.[sigma].
Proof with eauto using noccurs.
  move=> no. move: x m no sigma.
  apply: noccurs_ind_nested=>//=...
  move=> x y neq sigma [n _]...
  move=> x A B s noA ihA noB ihB sigma no.
    constructor...
    apply: ihB...
    apply: n_subst_up...
  move=> x A B s noA ihA noB ihB sigma no.
    constructor...
    apply: ihB...
    apply: n_subst_up...
  move=> x A m s noA ihA noM ihM sigma no.
    constructor...
    apply: ihM...
    apply: n_subst_up...
  move=> x A Cs s noA ihA noCs ihCs sigma no.
    constructor...
    elim: ihCs noCs; asimpl.
    constructor.
    move=> C Cs' hd tl ih1 ih2. inv ih2.
    constructor...
    apply: hd.
    apply: n_subst_up...
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs sigma no.
    constructor...
    elim: ihFs noFs; asimpl.
    constructor.
    move=> F Fs' hd tl ih1 ih2. inv ih2.
    constructor...
  move=> x m Q Fs noM ihM noQ ihQ noFs ihFs sigma no.
    constructor...
    elim: ihFs noFs; asimpl.
    constructor.
    move=> F Fs' hd tl ih1 ih2. inv ih2.
    constructor...
  move=> x A m noA ihA noM ihM sigma no.
    constructor...
    apply: ihM.
    apply: n_subst_up...
Qed.

Lemma pos_subst i A sigma :
  pos i A -> n_subst sigma i -> pos i A.[sigma].
Proof with eauto.
  move=> p. elim: p sigma=>//={i A}.
  move=> x ms noMs sigma [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: noMs.
    constructor.
    move=> m ms' noM noMs ihMs; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B s noA pB ihB sigma n.
    constructor.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B s noA pB ihB sigma n.
    constructor.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
Qed.

Lemma active_subst i m sigma :
  active i m -> n_subst sigma i -> active i m.[sigma].
Proof with eauto using List.Forall.
  move=> a. elim: a sigma=>{i m}=>//=.
  move=> x ms no sigma [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no...
    move=> m ms' hd tl ih; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B s p a ihB nB sigma n.
    apply: active_Pos.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B s noA a ihB sigma n.
    apply: active_Lolli.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
Qed.

Lemma constr_subst i s (m : term) sigma :
  constr i s m -> n_subst sigma i -> constr i s m.[sigma].
Proof with eauto.
  move=> c. elim: c sigma=>{i s m}=>//=.
  move=> x s ms no sigma [h e].
    rewrite spine_subst; asimpl.
    rewrite e.
    constructor.
    elim: no.
    constructor.
    move=> m ms' hd tl ih; asimpl.
    constructor...
    apply: noccurs_subst...
    split; eauto.
  move=> x A B p cB ihB nB sigma n.
    apply: constr_UPos.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B noA cB ihB sigma n.
    apply: constr_UProd.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B p cB ihB nB sigma n.
    apply: constr_LPos1.
    apply: pos_subst...
    apply: ihB.
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B p a noB sigma n.
    apply: constr_LPos2.
    apply: pos_subst...
    apply: active_subst...
    apply: n_subst_up...
    apply: noccurs_subst...
    apply: n_subst0.
  move=> x A B noA cB ihB sigma n.
    apply: constr_LProd1.
    apply: noccurs_subst...
    apply: ihB.
    apply: n_subst_up...
  move=> x A B noA a sigma n.
    apply: constr_LProd2.
    apply: noccurs_subst...
    apply: active_subst...
    apply: n_subst_up...
Qed.

Lemma arity1_subst s s' A sigma :
  arity s A -> (arity1 s' A).[sigma] = arity1 s' A.[sigma].
Proof.
  move=> a. elim: a sigma s'=>//={A}.
  move=> A B a ih sigma s'.
  rewrite ih; eauto.
Qed.

Lemma arity2_subst s s' I A sigma :
  arity s A -> (arity2 s' I A).[sigma] = arity2 s' I.[sigma] A.[sigma].
Proof.
  move=> a. elim: a I sigma s'=>//={A}.
  move=> A B a ih I sigma s'; asimpl.
  rewrite ih; asimpl; eauto.
Qed.

Lemma respine_I_subst Q I sigma :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  Q.[sigma] = respine Q.[sigma] I.[sigma].
Proof.
  elim: I sigma Q=>//=.
  move=> x sigma Q _ h.
    move: (h x)=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi Q h _.
    move: (h (Var 0))=>//=.
Qed.

Lemma drespine_I_subst Q c I sigma :
  (forall Q, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  App Q.[sigma] c.[sigma] = drespine Q.[sigma] c.[sigma] I.[sigma].
Proof.
  elim: I sigma Q=>//=.
  move=> x sigma Q _ h.
    move: (h x)=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> A _ B _ s sigma Q h _.
    move: (h (Var 0))=>//=.
  move=> m _ n _ xi Q h _.
    move: (h (Var 0))=>//=.
Qed.

Lemma respine_spine'_I_subst Q I ms sigma :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine Q (spine' I ms)).[sigma] =
    respine Q.[sigma] (spine' I ms).[sigma].
Proof.
  elim: ms Q I sigma=>//=.
  move=> Q I sigma h1 h2.
    rewrite h1.
    by apply: respine_I_subst.
  move=> m ms ih Q I xi h1 h2.
    rewrite ih; eauto.
Qed.

Lemma drespine_spine'_I_subst Q c I ms sigma :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  (drespine Q c (spine' I ms)).[sigma] =
    drespine Q.[sigma] c.[sigma] (spine' I ms).[sigma].
Proof.
  elim: ms Q I sigma=>//=.
  move=> Q I sigma h1 h2.
    rewrite h1.
    by apply: drespine_I_subst.
  move=> m ms ih Q I xi h1 h2.
    repeat f_equal.
    apply: respine_spine'_I_subst; eauto.
    by apply: drespine_respine.
Qed.

Lemma respine_spine_I_subst Q I ms sigma :
  (forall Q, respine Q I = Q) ->
  (forall x, ~I = Var x) ->
  (respine Q (spine I ms)).[sigma] =
    respine Q.[sigma] (spine I ms).[sigma].
Proof.
  move=> h1 h2.
  rewrite spine_spine'_rev.
  by rewrite respine_spine'_I_subst.
Qed.

Lemma drespine_spine_I_subst Q c I ms sigma :
  (forall Q c, drespine Q c I = App Q c) ->
  (forall x, ~I = Var x) ->
  (drespine Q c (spine I ms)).[sigma] =
    drespine Q.[sigma] c.[sigma] (spine I ms).[sigma].
Proof.
  move=> h1 h2.
  rewrite spine_spine'_rev.
  by rewrite drespine_spine'_I_subst.
Qed.

Lemma ren_Var_False (I : var -> term) x :
  (forall y, ~I x = Var y) -> (forall y, ~(I x).[ren (+1)] = Var y).
Proof.
  move e:(I x)=> n h y.
  elim: n h I e y; intros; try discriminate.
  destruct y; asimpl.
  discriminate.
  move: (h y)=>{}h eq.
  inv eq.
  apply: h; eauto.
Qed.

Lemma active_respine_subst n (Q C : term) I sigma :
  active n C ->
  (forall i Q, respine Q (I i) = Q) ->
  (forall x, ~I n = Var x) ->
  (respine Q C.[I]).[sigma] =
    respine Q.[sigma] C.[I].[sigma].
Proof.
  move=> c.
  elim: c Q I sigma; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.    
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: respine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: respine_up; eauto.
    apply: ren_Var_False; eauto.
Qed.

Lemma active_drespine_subst n (Q c C : term) I sigma :
  active n C ->
  (forall i c Q, drespine Q c (I i) = App Q c) ->
  (forall x, ~I n = Var x) ->
  (drespine Q c C.[I]).[sigma] =
    drespine Q.[sigma] c.[sigma] C.[I].[sigma].
Proof.
  move=> a.
  elim: a c Q I sigma; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.    
  - asimpl. repeat f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    apply: respine_up=> i.
    by apply: drespine_respine.
    move=> x'; asimpl.
    apply: ren_Var_False; eauto.
  - asimpl. repeat f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    apply: respine_up=> i.
    by apply: drespine_respine.
    move=> x'; asimpl.
    apply: ren_Var_False; eauto.
Qed.

Lemma constr_respine_subst n s (Q C : term) I sigma :
  constr n s C ->
  (forall i Q, respine Q (I i)= Q) ->
  (forall x, ~I n = Var x) ->
  (respine Q C.[I]).[sigma] =
    respine Q.[sigma] C.[I].[sigma].
Proof.
  move=> c.
  elim: c Q I sigma; intros.
  - rewrite! spine_subst.
    rewrite respine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: respine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: respine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: respine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    apply: respine_up; eauto.
    move=> x0; asimpl.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: respine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    erewrite active_respine_subst; asimpl; eauto.
    apply: respine_up; eauto.
    move=> x0; asimpl.
    apply: ren_Var_False; eauto.
Qed.

Lemma constr_drespine_subst n s (Q c C : term) I sigma :
  constr n s C ->
  (forall i c Q, drespine Q c (I i)= App Q c) ->
  (forall x, ~I n = Var x) ->
  (drespine Q c C.[I]).[sigma] =
    drespine Q.[sigma] c.[sigma] C.[I].[sigma].
Proof.
  move=> cn.
  elim: cn Q c I sigma; intros.
  - rewrite! spine_subst.
    rewrite drespine_spine_I_subst; eauto.
    rewrite! spine_subst; asimpl; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: drespine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: drespine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: drespine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    erewrite active_drespine_subst; asimpl; eauto.
    apply: drespine_up; eauto.
    move=> x0; asimpl.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    rewrite H1; asimpl; eauto.
    apply: drespine_up; eauto.
    apply: ren_Var_False; eauto.
  - asimpl. f_equal.
    erewrite active_drespine_subst; asimpl; eauto.
    apply: drespine_up; eauto.
    move=> x0; asimpl.
    apply: ren_Var_False; eauto.
Qed.

Lemma All2_case_subst Gamma Delta s A Q Fs Cs Cs' sigma :
  All2 (fun F C =>
    constr 0 s C /\
    forall Delta sigma, [ Delta |- sigma -| Gamma ] ->
      [ Delta |- F.[sigma] :- (case (Ind A Cs' s) Q C).[sigma] ])
    Fs Cs ->
  [ Delta |- sigma -| Gamma ] ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Delta |- F :- case (Ind A.[sigma] Cs'..[up sigma] s) Q.[sigma] C])
  Fs..[sigma] Cs..[up sigma].
Proof.
  elim: Fs Gamma Delta s A Q Cs sigma.
  move=> Gamma Delta s A Q Cs sigma h. inv h.
    constructor.
  move=> F Fs ih Gamma Delta s A Q Cs sigma h ag.
  destruct Cs; inv h. inv H2; asimpl.
  constructor. split.
  - apply: constr_subst; eauto.
    apply: n_subst0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold case in H0.
    erewrite constr_respine_subst in H0; eauto.
    asimpl in H0.
    by unfold case; asimpl.
    move=> i Q'.
    destruct i; asimpl; eauto.
    move=> x h. inv h.
  - apply: ih; eauto.
Qed.

Lemma All2i_dcase_subst Gamma Delta n s A Q Fs Cs Cs' sigma :
  All2i (fun i F C =>
    let I := Ind A Cs' s in
    constr 0 s C /\
    forall Delta sigma, [ Delta |- sigma -| Gamma ] ->
      [ Delta |- F.[sigma] :- (dcase I Q (Constr i I) C).[sigma] ])
    n Fs Cs ->
  [ Delta |- sigma -| Gamma ] ->
  All2i (fun i F C =>
    let I := Ind A.[sigma] Cs'..[up sigma] s in
    constr 0 s C /\
    [ Delta |- F :-dcase I Q.[sigma] (Constr i I) C ])
  n Fs..[sigma] Cs..[up sigma].
Proof.
  elim: Fs Gamma Delta n s A Q Cs sigma.
  move=> Gamma Delta n s A Q Cs sigma h. inv h.
    constructor.
  move=> F Fs ih Gamma Gamma' n s A Q Cs sigma h ag.
  destruct Cs; inv h. inv H3; asimpl.
  constructor. split.
  - apply: constr_subst; eauto.
    apply: n_subst0.
  - move: (H0 _ _ ag)=>{}H0.
    unfold dcase in H0.
    erewrite constr_drespine_subst in H0; eauto.
    asimpl in H0.
    by unfold dcase; asimpl.
    move=> i.
    destruct i; asimpl; eauto.
    move=> x h. inv h.
  - apply: ih; eauto.
Qed.

Lemma substitution Gamma Delta sigma m A :
  [ Gamma |- m :- A ] ->
  [ Delta |- sigma -| Gamma ] ->
  [ Delta |- m.[sigma] :- A.[sigma] ].
Proof with eauto using List.Forall.
  move=> ty. move: Gamma m A ty Delta sigma.
  apply: has_type_nested_ind=>//=.
  move=> Gamma s l p Delta sigma ag.
    apply: u_Sort.
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_u A ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: u_Prod...
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_n ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: l_Prod...
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_u A ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: u_Lolli...
    apply: agree_subst_pure...
  move=> Gamma A B s l p tyA ihA tyB ihB Delta sigma ag.
    move: (ihA _ _ ag)=>{}ihA.
    move: (agree_subst_n ag)=>ag'.
    move: (ihB _ _ ag')=>{}ihB.
    apply: l_Lolli...
    apply: agree_subst_pure...
  move=> Gamma x A h Delta sigma ag.
    apply: agree_subst_hasU...
  move=> Gamma x A h Delta sigam ag.
    apply: agree_subst_hasL...
  move=> Gamma n A B s t l p tyProd ihProd tyN ihN Delta sigma ag.
    destruct s.
    move: (agree_subst_u A ag)=>ag'.
      move: (ihN _ _ ag')=>{ag'}tyN.
      apply: u_Lam...
      apply: agree_subst_pure...
    move: (agree_subst_l A ag)=>ag'.
      move: (ihN _ _ ag')=>{ag'}tyN.
      apply: u_Lam...
      apply: agree_subst_pure...
  move=> Gamma n A B s t l tyLolli ihLolli tyN ihN Delta sigma ag.
    move: (agree_subst_re_re ag)=>ag'.
    move: (ihLolli _ _ ag')=>{}ihLolli.
    destruct s.
    move: (agree_subst_u A ag)=>{}ag.
      move: (ihN _ _ ag)=>{}ihN.
      apply: l_Lam...
    move: (agree_subst_l A ag)=>{}ag.
      move: (ihN _ _ ag)=>{}ihN.
      apply: l_Lam...
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma] 
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (agree_subst_pure ag2 p)=>{}p.
    apply: u_Prod_App...
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma]
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    apply: l_Prod_App...
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma] 
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (agree_subst_pure ag2 p)=>{}p.
    apply: u_Lolli_App...
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg Delta sigma ag.
    replace B.[n/].[sigma]
      with (B.[up sigma]).[n.[sigma]/]
      by autosubst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    apply: l_Lolli_App...
  move=> Gamma A s Cs l ar cs p tyA ihA tyCs ihCs Delta sigma ag.
    apply: s_Ind...
    apply: arity_subst...
    elim: cs; asimpl...
      move=> C Cs' c hd tl.
      constructor...
      apply: constr_subst...
      apply: n_subst0.
    apply: agree_subst_pure...
    elim: ihCs; asimpl...
      move=> C Cs' hd tl ih.
      constructor...
      apply: hd.
      constructor...
  move=> Gamma A s i C Cs ig p ty ih Delta sigma ag; asimpl.
    replace C.[Ind A.[sigma] Cs..[up sigma] s .: sigma]
      with C.[up sigma].[Ind A.[sigma] Cs..[up sigma] s/]
      by autosubst.
    apply: s_Constr...
    apply: iget_subst...
    apply: agree_subst_pure...
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms a mg
    tyM ihM tyQ ihQ tyFsCs ihFsCs Delta sigma ag.
    rewrite spine_subst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (arity_subst sigma a)=> a'.
    move: (agree_subst_re_re ag2)=> ag2'.
    move: (ihQ _ _ ag2')=> {}ihQ.
    erewrite arity1_subst in ihQ...
    move: (ihM _ _ ag1)=> {}ihM.
    rewrite spine_subst in ihM.
    apply: s_Case...
    apply: All2_case_subst...
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms a p mg
    tyM ihM tyQ ihQ tyFsCs ihFsCs Delta sigma ag.
    rewrite spine_subst.
    move: (merge_agree_subst_inv ag mg)=>[Delta1[Delta2[mg'[ag1 ag2]]]].
    move: (arity_subst sigma a)=> a'.
    move: (agree_subst_re_re ag2)=> ag2'.
    move: (ihQ _ _ ag2')=> {}ihQ.
    erewrite arity2_subst in ihQ...
    move: (ihM _ _ ag1)=> {}ihM.
    rewrite spine_subst in ihM.
    move: (agree_subst_pure ag1 p)=>{}p.
    apply: s_DCase...
    apply: All2i_dcase_subst...
  move=> Gamma A m l p tyA ihA tyM ihM Delta sigma ag.
    apply: u_Fix...
    apply: agree_subst_pure...
    have ag' : [ A.[sigma] +u Delta |- up sigma -| A +u Gamma ].
      by constructor.
    move: (ihM _ _ ag'); asimpl=>//.
  move=> Gamma A B m s l sub tyB ihB tyM ihM Delta sigma ag.
    apply: s_Conv.
    apply: sub_subst.
    apply: sub.
    apply: ihB.
    by apply: agree_subst_re_re.
    by apply: ihM.
Qed.

Lemma substitutionU Gamma1 Gamma2 Gamma m n A B :
  [ A +u Gamma1 |- m :- B ] ->
  [ Gamma2 |- n :- A ] ->
  pure Gamma2 ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN p mg.
  apply: substitution; eauto.
  move: (merge_pure2 mg p)=>->.
  apply: agree_subst_wkU.
  apply: agree_subst_refl.
  move: (merge_re_re mg)=>[-><-].
  asimpl.
  by rewrite <- pure_re.
Qed.

Lemma substitutionN Gamma1 Gamma2 m n A B :
  [ +n Gamma1 |- m :- B ] ->
  [ Gamma2 |- n :- A ] ->
  [ Gamma1 |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN.
  apply: substitution; eauto.
  apply: agree_subst_wkN.
  apply: agree_subst_refl.
Qed.

Lemma substitutionL Gamma1 Gamma2 Gamma m n A B :
  [ A +l Gamma1 |- m :- B ] ->
  [ Gamma2 |- n :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- m.[n/] :- B.[n/] ].
Proof.
  move=> tyM tyN mg.
  apply: substitution; eauto.
  apply: agree_subst_wkL; asimpl; eauto.
  apply: agree_subst_refl.
Qed.

Lemma context_convU Gamma m A B C l :
  B === A ->
  [ re Gamma |- A :- Sort U l ] ->
  [ A +u Gamma |- m :- C ] ->
  [ B +u Gamma |- m :- C ].
Proof.
  move=> e tyA tyM.
  cut [ B +u Gamma |- m.[ids] :- C.[ids] ]. 
    by autosubst.
  apply: substitution; eauto.
  apply: agree_subst_convU; asimpl.
  apply: conv_sub; eauto.
  move: (weakeningU B tyA); asimpl; eauto.
  apply: agree_subst_refl.
Qed.

Lemma context_convL Gamma m A B C l :
  B === A ->
  [ re Gamma |- A :- Sort L l ] ->
  [ A +l Gamma |- m :- C ] ->
  [ B +l Gamma |- m :- C ].
Proof.
  move=> e tyA tyB.
  cut [ B +l Gamma |- m.[ids] :- C.[ids] ].
    by autosubst.
  apply: substitution; eauto.
  apply: agree_subst_convL; asimpl.
  apply: conv_sub; eauto.
  move: (weakeningN tyA); asimpl; eauto.
  eauto.
  apply: agree_subst_refl.
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

Lemma u_Sort_inv Gamma s l A :
  [ Gamma |- s @ l :- A ] -> U @ l.+1 <: A.
Proof.
  move e:(s @ l)=> n ty. elim: ty s l e=>//={Gamma A n}.
  move=> Gamma s l p s' l' [_ ->]; eauto.
  move=> Gamma A B m s l sb _ _ _ ihM s' l' /ihM sb'.
    apply: sub_trans; eauto.
Qed.

Lemma u_Var_inv Gamma x B :
  [ Gamma |- Var x :- B ] -> 
  (exists A, hasU Gamma x A /\ A <: B) \/
  (exists A, hasL Gamma x A /\ A <: B).
Proof.
  move e:(Var x)=> v ty.
  move: Gamma v B ty x e.
  apply: has_type_nested_ind; intros; try discriminate.
  - inv e.
    left. exists A; eauto.
  - inv e.
    right. exists A; eauto.
  - subst.
    have e : Var x = Var x by eauto.
    move: (H3 _ e)=>[[A0[hA sb]]|[A0[hA sb]]].
    left. exists A0. firstorder. apply: sub_trans; eauto.
    right. exists A0. firstorder. apply: sub_trans; eauto.
Qed.

Lemma l_Var_inv Gamma A B :
  [ A +l Gamma |- Var 0 :- B ] -> A.[ren (+1)] <: B.
Proof.
  move e1:(A +l Gamma)=> Delta.
  move e2:(Var 0)=> v ty.
  move: Delta v B ty Gamma A e1 e2.
  apply: has_type_nested_ind; intros; try discriminate.
  - inv e2.
    inv H; eauto.
  - inv e2.
    inv H; eauto.
  - inv e2.
    apply: sub_trans.
    apply: H3; eauto.
    apply: H.
Qed.

Lemma u_Prod_inv Gamma A B C :
  [ Gamma |- Prod A B U :- C ] ->
  exists s l l',
    [ Gamma |- A :- Sort U l ] /\ 
    [ A +u Gamma |- B :- Sort s l ] /\
    Sort U l' <: C.
Proof.
  move e:(Prod A B U)=> n ty. elim: ty A B e =>//={Gamma n}.
  move=> Gamma A B s l p tyA _ tyB _ A' B' [->->].
    exists s. 
    exists l.
    exists l.
    eauto.
  move=> Gamma A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma l_Prod_inv Gamma A B C :
  [ Gamma |- Prod A B L :- C ] ->
  exists s l l',
    [ Gamma |- A :- Sort L l ] /\ 
    [ +n Gamma |- B :- Sort s l ] /\
    Sort U l' <: C.
Proof.
  move e:(Prod A B L)=> n ty. elim: ty A B e=>//={Gamma n}.
  move=> Gamma A B s l p tyA ihA tyB ihB A' B' [->->].
    exists s.
    exists l.
    exists l.
    eauto.
  move=> Gamma A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma u_Lolli_inv Gamma A B C :
  [ Gamma |- Lolli A B U :- C ] ->
  exists s l l',
    [ Gamma |- A :- Sort U l ] /\ 
    [ A +u Gamma |- B :- Sort s l ] /\
    Sort L l' <: C.
Proof.
  move e:(Lolli A B U)=> n ty. elim: ty A B e=>//={Gamma n}.
  move=> Gamma A B s l p tyA ihA tyB ihB A' B' [->->].
    exists s.
    exists l.
    exists l.
    eauto.
  move=> Gamma A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma l_Lolli_inv Gamma A B C :
  [ Gamma |- Lolli A B L :- C ] ->
  exists s l l',
    [ Gamma |- A :- Sort L l ] /\ 
    [ +n Gamma |- B :- Sort s l ] /\
    Sort L l' <: C.
Proof.
  move e:(Lolli A B L)=> n ty. elim: ty A B e=>//={Gamma n}.
  move=> Gamma A B s l p tyA ihA tyB ihB A' B' [->->].
    exists s.
    exists l.
    eauto.
  move=> Gamma A B m s l sb tyB ihB tyM ihM A' B' e; subst.
    move: (ihM A' B'); firstorder.
    exists x.
    exists x0.
    exists x1.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma u_Lam_invX Gamma A0 A1 B C s0 s1 m t l :
  [ Gamma |- Lam A0 m s0 :- C ] ->
  (C <: Prod A1 B s1 /\ [ re (A1 +{s1} Gamma) |- B :- Sort t l ]) ->
  [ A1 +{s1} Gamma |- m :- B ].
Proof.
  move e:(Lam A0 m s0)=> n ty. 
  elim: ty A0 A1 B s0 s1 t l e=>{Gamma C n}; intros; try discriminate.
  inv e. inv H4.
    move: (sub_Prod_inv H5)=>[_[sb e]]; subst.
    move: (pure_re H)=> e.
    rewrite e in H0.
    destruct s1.
    move: H0=>/u_Prod_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H5=>/sub_Prod_inv[eA _].
      apply: context_convU.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H2.
    move: H0=>/l_Prod_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H5=>/sub_Prod_inv[eA _].
      apply: context_convL.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H2.
  inv H3. exfalso; solve_sub.
  inv H4.
    apply: H3; eauto.
    split; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma l_Lam_invX Gamma A0 A1 B C s0 s1 m t l :
  [ Gamma |- Lam A0 m s0 :- C ] ->
  (C <: Lolli A1 B s1 /\ [ re (A1 +{s1} Gamma) |- B :- Sort t l ]) ->
  [ A1 +{s1} Gamma |- m :- B ].
Proof.
  move e:(Lam A0 m s0)=> n ty.
  elim: ty A0 A1 B s0 s1 t l e=>{Gamma C n}; intros; try discriminate.
  inv H4. exfalso; solve_sub.
  inv e. inv H3.
    move: (sub_Lolli_inv H4)=>[_[sb e]]; subst.
    destruct s1.
    move: H=>/u_Lolli_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H4=>/sub_Lolli_inv[eA _].
      apply: context_convU.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H1.
    move: H=>/l_Lolli_inv[s[l1[l2[tyA [tyB _]]]]].
      apply: s_Conv; eauto.
      move: H4=>/sub_Lolli_inv[eA _].
      apply: context_convL.
      apply: conv_sym.
      apply: eA.
      apply tyA.
      apply: H1.
  inv H4.
    apply: H3; eauto.
    split; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma u_Lam_inv Gamma A0 A1 B s0 s1 m t l :
  [ re Gamma |- Prod A1 B s1 :- Sort t l ] ->
  [ Gamma |- Lam A0 m s0 :- Prod A1 B s1 ] ->
  [ A1 +{s1} Gamma |- m :- B ].
Proof.
  destruct s1.
  move=> /u_Prod_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: u_Lam_invX; eauto.
  move=> /l_Prod_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: u_Lam_invX; eauto.
Qed.

Lemma l_Lam_inv Gamma A0 A1 B s0 s1 m t l :
  [ re Gamma |- Lolli A1 B s1 :- Sort t l ] ->
  [ Gamma |- Lam A0 m s0 :- Lolli A1 B s1 ] ->
  [ A1 +{s1} Gamma |- m :- B ].
Proof.
  destruct s1.
  move=> /u_Lolli_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: l_Lam_invX; eauto.
  move=> /l_Lolli_inv=>[[s[l1[l2[tyA [tyB _]]]]] ty].
    apply: l_Lam_invX; eauto.
Qed.

Lemma s_Ind_invX Gamma A B Cs s :
  [ Gamma |- Ind A Cs s :- B ] ->
  exists l,
    A <: B /\
    arity s A /\
    List.Forall (constr 0 s) Cs /\
    pure Gamma /\
    [ Gamma |- A :- Sort U l ] /\
    List.Forall (fun C => [ A +u Gamma |- C :- Sort U l ]) Cs.
Proof.
  move e:(Ind A Cs s)=> n ty.
  elim: ty Cs e=>{Gamma n}; intros; try discriminate.
  inv e. exists l. firstorder.
  move: (H3 _ e)=>[l'[sb h]].
    exists l'. firstorder.
    apply: sub_trans.
    apply: sb.
    apply: H.
Qed.

Lemma s_Ind_inv Gamma A Cs s :
  [ Gamma |- Ind A Cs s :- A ] ->
  exists l,
    arity s A /\
    List.Forall (constr 0 s) Cs /\
    pure Gamma /\
    [ Gamma |- A :- Sort U l ] /\
    List.Forall (fun C => [ A +u Gamma |- C :- Sort U l ]) Cs.
Proof. move=> /s_Ind_invX; firstorder. Qed.

Lemma s_Constr_invX Gamma i I CI :
  [ Gamma |- Constr i I :- CI ] ->
  exists A C Cs s,
    iget i Cs C /\
    pure Gamma /\
    I = Ind A Cs s /\
    C.[I/] <: CI /\
    [ Gamma |- I :- A ].
Proof.
  move e:(Constr i I)=> n ty.
  elim: ty i I e=>{Gamma CI n}; intros; try discriminate.
  - inv e. 
    exists A.
    exists C.
    exists Cs.
    exists s.
    eauto.
  - subst.
    have e : Constr i I = Constr i I by eauto.
    move: (H3 i I e)=>[A0[C[Cs[s0[ig[p[->[sb tyI]]]]]]]].
    exists A0.
    exists C.
    exists Cs.
    exists s0.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma iget_Forall i P C Cs:
  iget i Cs C -> List.Forall (fun C => P C) Cs -> P C.
Proof.
  elim=>{i C Cs}.
  move=> C Cs tyCs. by inv tyCs.
  move=> i C C' Cs ig ih tyCs.
    inv tyCs.
    apply: ih; eauto.
Qed.

Inductive arity_spine : 
  context term -> term -> list term -> term -> Prop :=
| arity_spine_nil Gamma A s l :
  pure Gamma ->
  [ Gamma |- A :- Sort s l ] ->
  arity_spine Gamma A nil A
| arity_spine_u_Prod_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  pure Gamma1 ->
  [ Gamma1 |- Prod A B U :- Sort U l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Prod A B U) (hd :: tl) B'
| arity_spine_l_Prod_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  [ re Gamma1 |- Prod A B L :- Sort U l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Prod A B L) (hd :: tl) B'
| arity_spine_u_Lolli_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  pure Gamma1 ->
  [ Gamma1 |- Lolli A B U :- Sort L l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Lolli A B U) (hd :: tl) B'
| arity_spine_l_Lolli_cons Gamma1 Gamma2 Gamma hd tl A B B' l :
  [ re Gamma1 |- Lolli A B L :- Sort L l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma2 B.[hd/] tl B' ->
  arity_spine Gamma (Lolli A B L) (hd :: tl) B'.

Lemma App_arity_spine Gamma1 Gamma2 Gamma m ms A B :
  [ Gamma1 |- m :- A ] ->
  arity_spine Gamma2 A ms B ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- spine m ms :- B ].
Proof.
  move=> tyM tsp. elim: tsp Gamma1 Gamma m tyM=>//={Gamma2 A ms B}.
  move=> Gamma2 A s l p tyA Gamma1 Gamma m tyM mg.
    move: (merge_pure2 mg p)=>->//=.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p 
    tyProd tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Prod_App; eauto.
    move: (merge_re2 Gamma1').
    rewrite e1'.
    rewrite <- e2'.
    rewrite <- e1.
    rewrite <- pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l 
    tyProd tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[GammaX[mg1 mg2]].
    apply: ih; eauto.
    apply: l_Prod_App; eauto.
    apply: merge_sym; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p 
    tyLolli tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Lolli_App; eauto.
    move: (merge_re2 Gamma1').
    rewrite e1'.
    rewrite <- e2'.
    rewrite <- e1.
    rewrite <- pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l 
    tyLolli tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[GammaX[mg1 mg2]].
    apply: ih; eauto.
    apply: l_Lolli_App; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_arity1_ok Gamma A B s s' t l :
  [ Gamma |- A :- B ] -> 
  B <: s @ l ->
  arity s' A ->
  exists t', 
    [ Gamma |- arity1 t A :- t' @ l ].
Proof.
  move=> ty. elim: ty s s' t l; intros;
  match goal with
  | [ H : arity _ _ |- _ ] => try solve [inv H]
  end=>//=.
  exists U. 
    move: H0=>/sub_Sort_inv[_ lt].
    have sb : U @ l.+1 <: U @ l0.
      apply: sub_Sort; eauto.
    apply: s_Conv.
    apply: sb.
    constructor.
    apply re_pure.
    constructor; eauto.
  inv H5.
    have sb : s @ l <: s @ l by eauto.
    move: (H3 s s' t l sb H7)=>[t' ty].
    exists U.
    move: H4=>/sub_Sort_inv[_ lte].
    apply: u_Prod; eauto.
    apply: s_Conv.
    apply: sub_Sort; eauto.
    constructor.
    apply re_pure.
    apply H0.
    apply: s_Conv.
    apply: sub_Sort; eauto.
    constructor.
    apply re_pure.
    apply ty.
  apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma arity_arity2_ok Gamma A B I s t l :
  [ Gamma |- A :- B ] ->
  B <: s @ l ->
  arity U A ->
  [ Gamma |- I :- A ] ->
  exists t', 
    [ Gamma |- arity2 t I A :- t' @ l ].
Proof.
  move=> ty. elim: ty s t l I; intros;
  match goal with
  | [ H : arity _ _ |- _ ] => try solve [inv H]
  end=>//=.
  exists U.
    move: H0=>/sub_Sort_inv[_ lt]. inv H1.
    have sb1 : U @ l <: U @ l0.
      apply: sub_Sort; eauto.
    have sb2 : U @ l.+1 <: U @ l0.
      apply: sub_Sort; eauto.
    apply: u_Prod; eauto.
    apply: s_Conv.
    apply: sb1.
    constructor. apply re_pure.
    apply: H2.
    apply: s_Conv.
    apply: sb2.
    constructor. apply re_pure.
    repeat constructor; eauto.
  inv H5.
    have sb : s @ l <: s @ l by eauto.
    have ty0 : [ A0 +u Gamma0 |- Var 0 :- A0.[ren (+1)] ].
      apply: u_Var.
      constructor; eauto.
    have //=tyIw : [ A0 +u Gamma0 |- I.[ren (+1)] :- (Prod A0 B0 U).[ren (+1)] ].
      apply: eweakeningU; eauto.
    have p2 : pure (A0 +u Gamma0) by constructor.
    have mg : merge (A0 +u Gamma0) (A0 +u Gamma0) (A0 +u Gamma0).
      constructor.
      apply: merge_pure; eauto.
    move: (u_Prod_App p2 tyIw ty0 mg); asimpl=> tyIx.
    move: (H3 s t l _ sb H8 tyIx)=>[t' ty].
    exists U.
    move: H4=>/sub_Sort_inv[_ lt].
    have sbx : U @ l <: U @ l0.
      apply: sub_Sort; eauto.
    apply: s_Conv.
    apply: sbx.
    constructor. apply: re_pure.
    apply: u_Prod; eauto.
  apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Lemma arity1_spine Gamma ms A s s' t l :
  arity_spine Gamma A ms (Sort s l) ->
  arity s' A ->
  pure Gamma ->
  arity_spine Gamma (arity1 t A) ms (Sort t l).
Proof.
  move e:(Sort s l)=> n tsp. 
  elim: tsp s l e t=>//={Gamma n A ms}.
  move=> Gamma A s l p tyA s0 l0 e t a _; subst.
    inv a=>//=.
    apply: arity_spine_nil; eauto.
    constructor; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l _
    tyProd tyHd mg sp ih s0 l0 e t a p'; subst.
    inv a=>//=.
    move: (merge_pure_inv mg p')=>[p1 p2].
    move: (merge_pure1 mg p1)=>e1.
    move: (merge_pure2 mg p2)=>e2.
    subst.
    have e : s0 @ l0 = s0 @ l0 by eauto.
    have a : arity s' B.[hd/].
      apply: arity_subst; eauto.
    move: (ih s0 l0 e t a)=> h.
    apply u_Prod_inv in tyProd; firstorder.
    have sb : x @ x0 <: x @ x0 by eauto.
    move: (arity_arity1_ok t H1 sb H0)=>[t' ty].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: u_Prod; eauto.
    erewrite arity1_subst; eauto.
  intros. inv H4.
  intros. inv H5.
  intros. inv H4.
Qed.

Lemma arity2_spine Gamma ms I A s t l :
  arity_spine Gamma A ms (Sort s l) ->
  arity U A ->
  pure Gamma ->
  [ Gamma |- I :- A ] ->
  arity_spine Gamma 
    (arity2 t I A) ms (Prod (spine I ms) (Sort t l) U).
Proof.
  move e:(Sort s l)=> n tsp. 
  elim: tsp I s l e t=>//={Gamma n A ms}.
  move=> Gamma A s l p tyA I s0 l0 e t a _ tyI; subst.
    inv a=>//=.
    have sb : U @ l0 <: U @ l0.+1.
      by apply: sub_Sort.
    apply: arity_spine_nil; eauto.
    apply: u_Prod.
    apply: p.
    apply: s_Conv.
    apply: sb.
    constructor; eauto.
    apply: re_pure.
    apply: tyI.
    constructor; eauto.
    constructor; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p
    tyProd tyHd mg sp ih I s0 l0 e t a p' tyI; subst.
    inv a=>//=.
    move: (merge_pure_inv mg p')=>[p1 p2].
    move: (merge_pure1 mg p1)=>e1.
    move: (merge_pure2 mg p2)=>e2.
    subst.
    have e : s0 @ l0 = s0 @ l0 by eauto.
    have a : arity U B.[hd/].
      apply: arity_subst; eauto.
    have ty : [ Gamma1 |- App I hd :- B.[hd/] ].
      apply: u_Prod_App; eauto.
    move: (ih (App I hd) s0 l0 e t a p ty)=> h.
    apply u_Prod_inv in tyProd; firstorder.
    have sb : x @ x0 <: x @ x0 by eauto.
    have pA : pure (A +u Gamma1).
      constructor; eauto.
    have //=tyI' : [ A +u Gamma1 |- I.[ren (+1)] :- (Prod A B U).[ren (+1)] ].
      apply: eweakeningU; eauto.
    have ty0 : [ A +u Gamma1 |- Var 0 :- A.[ren (+1)] ].
      apply: u_Var.
      constructor; eauto.
    have mgA : merge (A +u Gamma1) (A +u Gamma1) (A +u Gamma1).
      constructor.
      apply: merge_pure; eauto.
    move: (u_Prod_App pA tyI' ty0 mgA); asimpl=>{pA}tyApp.
    move: (arity_arity2_ok t H1 sb H0 tyApp)=>[t' ty'].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: u_Prod; eauto.
    erewrite arity2_subst; asimpl; eauto.
  intros. inv H4.
  intros. inv H5.
  intros. inv H4.
Qed.

Ltac solve_Ind_spine' :=
  match goal with 
  | [ H : spine' (Ind _ _ _) ?ms = _ |- _ ] =>
    induction ms; simpl; intros; discriminate
  | [ H : _ = spine' (Ind _ _ _) ?ms  |- _ ] =>
    induction ms; simpl; intros; discriminate
  end.

Lemma arity_spine_u_Prod_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Prod B C U) ->
  pure Gamma2 ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Prod B C U)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Prod_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H3 H1)=>e2.
    destruct s.
    apply: arity_spine_u_Prod_cons.
      apply: H.
      apply: H0.
      rewrite<-e2. rewrite e1; eauto.
      apply: H3.
      move: (substitutionU tyC H2 H1 H3)=>//=tyCN.
      apply: arity_spine_nil; eauto.
      rewrite<-e1; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Prod_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_l_Prod_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Prod B C L) ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Prod B C L)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Prod_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H2)=>[e1 e2].
    destruct s.
    apply: arity_spine_l_Prod_cons.
      2:{ apply: H1. }
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H1)=>//=tyCN.
      apply: arity_spine_nil; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_u_Lolli_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Lolli B C U) ->
  pure Gamma2 ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C U)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Lolli_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H3 H1)=>e2.
    destruct s.
    exfalso. apply: sub_Sort_False2; eauto.
    apply: arity_spine_u_Lolli_cons.
      apply: H.
      apply: H0.
      rewrite<-e2. rewrite e1; eauto.
      apply: H3.
      move: (substitutionU tyC H2 H1 H3)=>//=tyCN.
      apply: arity_spine_nil; eauto.
      rewrite<-e1; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Prod_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_pure1 H2 H)=>e1.
    move: (merge_pure2 H7 H5)=>e2.
    subst.
    apply: arity_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H4; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma arity_spine_l_Lolli_rcons Gamma1 Gamma2 Gamma A B C n ms :
  arity_spine Gamma1 A ms (Lolli B C L) ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  arity_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C L)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Lolli_inv H0)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H2)=>[e1 e2].
    destruct s.
    exfalso. apply: sub_Sort_False2; eauto.
    apply: arity_spine_l_Lolli_cons.
      2:{ apply: H1. }
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H1)=>//=tyCN.
      apply: arity_spine_nil; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H1)=>mg.
    move: (merge_merge mg H5)=>[Gamma4[mg1 mg2]].
    apply: arity_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma s_Ind_spine'_invX Gamma A B Cs ms s :
  pure Gamma ->
  arity s A ->
  [ Gamma |- spine' (Ind A Cs s) ms :- B ] ->
  exists A' s t l,
    arity t A' /\
    [ Gamma |- A' :- s @ l ] /\
    arity_spine Gamma A (rev ms) A' /\
    A' <: B.
Proof.
  move e:(spine' (Ind A Cs s) ms)=> n p a ty. 
  elim: ty A Cs ms s p a e=>{Gamma n}; intros; 
  try solve [exfalso; solve_Ind_spine'].
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure1 H4 p1)=> e1.
    move: (merge_pure2 H4 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H1 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    move: sb=>/sub_Prod_inv[e[sb _]].
    move: ty=>/u_Prod_inv[x[lx[_[tyA1[tyB1 _]]]]].
    exists B1.[n/]. exists x. exists t'. exists lx.
    have tyN : [ Gamma1 |- n :- A1 ].
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply e.
      rewrite <- pure_re; eauto.
      apply: H2.
    repeat split.
    apply: arity_subst; eauto.
    replace (x @ lx) with (x @ lx).[n/] by autosubst.
    apply: substitutionU; eauto.
    rewrite rev_cons.
    apply: arity_spine_u_Prod_rcons; eauto.
    apply: sub_subst; eauto.
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure1 H3 p1)=> e1.
    move: (merge_pure2 H3 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H0 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    move: sb=>/sub_Prod_inv[e[sb _]].
    move: ty=>/u_Prod_inv[x[lx[_[tyA1[tyB1 _]]]]].
    exists B1.[n/]. exists x. exists t'. exists lx.
    have tyN : [ Gamma1 |- n :- A1 ].
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply e.
      rewrite <- pure_re; eauto.
      apply: H1.
    repeat split.
    apply: arity_subst; eauto.
    replace (x @ lx) with (x @ lx).[n/] by autosubst.
    apply: substitutionU; eauto.
    rewrite rev_cons.
    apply: arity_spine_u_Prod_rcons; eauto.
    apply: sub_subst; eauto.
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure1 H4 p1)=> e1.
    move: (merge_pure2 H4 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H1 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    exfalso; solve_sub.
  move: e; destruct ms.
    rewrite /rev/catrev=>//=.
    move=>//=e. inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure1 H3 p1)=> e1.
    move: (merge_pure2 H3 p2)=> e2.
    have eInd : spine' (Ind A0 Cs s) ms = spine' (Ind A0 Cs s) ms.
      by eauto.
    move: (H0 _ _ _ _ p1 a eInd)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    inv a'.
    exfalso; solve_sub.
    exfalso; solve_sub.
  destruct ms; simpl in e.
    inv e.
    rewrite /rev/catrev.
    exists A. exists U. exists s. exists l.
    repeat split; eauto.
    apply: arity_spine_nil; eauto.
    inv e.
  move:(H3 A0 Cs ms s0 p a e)=>[A'[s'[t'[l'[a'[ty [sp sb]]]]]]].
    exists A'. exists s'. exists t'. exists l'.
    firstorder.
    apply: sub_trans; eauto.
Qed.

Lemma s_Ind_spine_invX Gamma A B Cs ms s :
  pure Gamma ->
  arity s A ->
  [ Gamma |- spine (Ind A Cs s) ms :- B ] ->
  exists A' s t l,
    arity t A' /\
    [ Gamma |- A' :- s @ l ] /\
    arity_spine Gamma A ms A' /\
    A' <: B.
Proof.
  move=> p a ty.
  rewrite spine_spine'_rev in ty.
  apply s_Ind_spine'_invX in ty; eauto.
  rewrite revK in ty; eauto.
Qed.

Lemma s_Ind_spine_inv Gamma A Cs ms s t l :
  pure Gamma ->
  arity s A ->
  [ Gamma |- spine (Ind A Cs s) ms :- t @ l ] ->
  exists s l, arity_spine Gamma A ms (s @ l).
Proof.
  move=> p a ty.
  move: (s_Ind_spine_invX p a ty)=>[A'[s'[t'[l'[a'[tyA'[sp sb]]]]]]].
  inv a'.
  exists t'. exists l0. eauto.
  exfalso. solve_sub.
Qed.

Lemma s_Ind_spine' Gamma A B Cs s ms :
  pure Gamma ->
  [ Gamma |- spine' (Ind A Cs s) ms :- B ] ->
  [ Gamma |- Ind A Cs s :- A ].
Proof.
  move e:(spine' (Ind A Cs s) ms)=> n p ty.
  elim: ty A Cs s ms p e=>//{Gamma B n}; intros; 
  try solve [destruct ms; simpl in e; try inv e].
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure2 H4 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure2 H3 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H4 p)=>[p1 p2].
    move: (merge_pure2 H4 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    move: (merge_pure_inv H3 p)=>[p1 p2].
    move: (merge_pure2 H3 p2)=>->; eauto.
  - destruct ms; simpl in e; inv e.
    econstructor; eauto.
  - destruct ms0; simpl in e; inv e.
  - destruct ms0; simpl in e; inv e.
Qed.

Lemma s_Ind_spine Gamma A B Cs s ms :
  pure Gamma ->
  [ Gamma |- spine (Ind A Cs s) ms :- B ] ->
  [ Gamma |- Ind A Cs s :- A ].
Proof.
  rewrite spine_spine'_rev=> p ty.
  by move: (s_Ind_spine' p ty).
Qed.

Lemma merge_context_ok_inv Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- ] ->
  [ Gamma1 |- ] /\ [ Gamma2 |- ].
Proof.
  elim=>{Gamma1 Gamma2 Gamma}//=.
  move=> Gamma1 Gamma2 Gamma m mg ih h. inv h.
    move: (ih H1)=>{H1 ih}[h1 h2].
    move: (merge_re_re mg)=>[e1 e2].
    split.
    apply: u_ok; eauto. rewrite e1; eauto.
    apply: u_ok; eauto. rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma m mg ih h. inv h.
    move: (ih H1)=>{H1 ih}[h1 h2].
    move: (merge_re_re mg)=>[e1 e2].
    split.
    apply: l_ok; eauto. rewrite e1; eauto.
    apply: n_ok; eauto.
  move=> Gamma1 Gamma2 Gamma m mg ih h. inv h.
    move: (ih H1)=>{H1 ih}[h1 h2].
    move: (merge_re_re mg)=>[e1 e2].
    split.
    apply: n_ok; eauto.
    apply: l_ok; eauto. rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma mg ih h. inv h.
    move: (ih H0)=>{H0 ih}[h1 h2].
    repeat constructor; eauto.
Qed.

Theorem propagation Gamma m A :
  [ Gamma |- ] ->
  [ Gamma |- m :- A ] ->
  exists s l, [ re Gamma |- A :- Sort s l ].
Proof.
  move=> wf ty. move: Gamma m A ty wf.
  apply: has_type_nested_ind=>//=; eauto.
  move=> Gamma _ l p wf.
    exists U. exists (l.+2).
    constructor.
    rewrite <- pure_re; eauto.
  move=> Gamma _ _ _ l p _ _ _ _ wf.
    exists U. exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  move=> Gamma _ _ _ l p _ _ _ _ wf.
    exists U. exists (l.+1).
    constructor.
    rewrite <- pure_re; eauto.
  move=> Gamma x A h wf.
    exists U. apply: hasU_ok; eauto.
  move=> Gamma x A h wf.
    exists L. apply: hasL_ok; eauto.
  move=> Gamma n A B s t l p tyProd _ _ _ _.
    exists t. exists l.
    rewrite <- pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf.
    move: (merge_pure2 mg p)=>->.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /u_Prod_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionU; eauto.
    replace Gamma2 with (re Gamma1).
    apply: merge_re_re_re.
    move: (pure_re p)=>->.
    rewrite e1 e2; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /l_Prod_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionN; eauto.
    rewrite <- e1; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf.
    move: (merge_pure2 mg p)=>->.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /u_Lolli_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionU; eauto.
    replace Gamma2 with (re Gamma1).
    apply: merge_re_re_re.
    move: (pure_re p)=>->.
    rewrite e1 e2; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf.
    move: (merge_re_re mg)=>[e1 e2].
    have [wf1 wf2] := merge_context_ok_inv mg wf.
    move: (ihM wf1)=>{ihM}[s[l /l_Lolli_inv[s'[l'[_[tyA [tyB _]]]]]]].
    exists s'. exists l'.
    replace (Sort s' l') with (Sort s' l').[n/] by autosubst.
    apply: substitutionN; eauto.
    rewrite <- e1; eauto.
  move=> Gamma A s Cs l a c p tyA ihA tyCs ihCs wf.
    exists U. exists l.
    rewrite <- pure_re; eauto.
  move=> Gamma A s i C Cs ig p tyInd ihInd wf.
    move: (s_Ind_inv tyInd)=>[l'[_[c[_[tyA tyCs]]]]].
    exists U. exists l'.
    move: (iget_Forall ig tyCs)=>tyC.
    replace (Sort U l') with (Sort U l').[Ind A Cs s/] by autosubst.
    apply: substitutionU; eauto.
    rewrite <- pure_re; eauto.
    apply: merge_pure; eauto.
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms a mg 
    tyM ihM tyQ _ _ _ wf.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: wf1=>/ihM{ihM}[s1[l1 tyInd]].
    have p : pure (re Gamma1) by apply: re_pure.
    move: (merge_re_re mg)=>[e1 e2].
    apply s_Ind_spine_inv in tyInd; eauto.
    move: tyInd=>[sx[lx sp]].
    move: (@arity1_spine (re Gamma1) ms A sx s s' lx sp a p)=>{}sp.
    rewrite e2 in tyQ. rewrite <- e1 in tyQ.
    move: (merge_re_re_re Gamma1)=>mg1.
    move: (App_arity_spine tyQ sp mg1)=>tySp.
    exists s'. exists lx. rewrite <-e1; eauto.
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms _ p mg 
    tyM ihM tyQ _ _ _ wf.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: wf1=>/ihM{ihM}[s1[l1 tySpInd]].
    have pr : pure (re Gamma1) by apply: re_pure.
    move: (merge_re_re mg)=>[e1 e2].
    move: (s_Ind_spine pr tySpInd)=>tyInd.
    move: (s_Ind_inv tyInd)=>[l[a[_[_[tyA _]]]]].
    apply s_Ind_spine_inv in tySpInd; eauto.
    move: tySpInd=>[sx[lx sp]].
    move: (@arity2_spine (re Gamma1) ms 
      (Ind A Cs U) A sx s' lx sp a pr tyInd)=>{}sp.
    rewrite e2 in tyQ. rewrite <- e1 in tyQ.
    move: (merge_re_re_re Gamma1)=>mg1.
    move: (App_arity_spine tyQ sp mg1)=>tySp.
    exists s'. exists lx.
    replace (s' @ lx) with (s' @ lx).[m/] by autosubst.
    apply: u_Prod_App; eauto.
    rewrite <- pure_re; eauto.
    rewrite e1. apply: merge_re_re_re.
  move=> Gamma A m l p tyA ihA tyM ihM wf.
    exists U. exists l.
    rewrite <- pure_re; eauto.
Qed.

Inductive typing_spine : 
  context term -> term -> list term -> term -> Prop :=
| typing_spine_nil Gamma A B s l :
  pure Gamma ->
  A <: B ->
  [ Gamma |- B :- Sort s l ] ->
  typing_spine Gamma A nil B
| typing_spine_u_Prod_cons Gamma1 Gamma2 Gamma hd tl T A B B' l :
  pure Gamma1 ->
  T <: Prod A B U ->
  [ Gamma1 |- Prod A B U :- Sort U l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma2 B.[hd/] tl B' ->
  typing_spine Gamma T (hd :: tl) B'
| typing_spine_l_Prod_cons Gamma1 Gamma2 Gamma hd tl T A B B' l :
  T <: Prod A B L ->
  [ re Gamma1 |- Prod A B L :- Sort U l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma2 B.[hd/] tl B' ->
  typing_spine Gamma T (hd :: tl) B'
| typing_spine_u_Lolli_cons Gamma1 Gamma2 Gamma hd tl T A B B' l :
  pure Gamma1 ->
  T <: Lolli A B U ->
  [ Gamma1 |- Lolli A B U :- Sort L l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma2 B.[hd/] tl B' ->
  typing_spine Gamma T (hd :: tl) B'
| typing_spine_l_Lolli_cons Gamma1 Gamma2 Gamma hd tl T A B B' l :
  T <: Lolli A B L ->
  [ re Gamma1 |- Lolli A B L :- Sort L l ] ->
  [ Gamma1 |- hd :- A ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma2 B.[hd/] tl B' ->
  typing_spine Gamma T (hd :: tl) B'.

Lemma arity_typing_spine Gamma A ms B :
  arity_spine Gamma A ms B -> typing_spine Gamma A ms B.
Proof.
  move=>a. elim: a=>{Gamma A ms B}.
  move=> Gamma A s l p tyA.
    apply: typing_spine_nil; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p tyProd tyHd mg a tySp.
    apply: typing_spine_u_Prod_cons; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l tyProd tyHd mg a tySp.
    apply: typing_spine_l_Prod_cons; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l p tyLolli tyHd mg a tySp.
    apply: typing_spine_u_Lolli_cons; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl A B B' l tyProd tyHd mg a tySp.
    apply: typing_spine_l_Lolli_cons; eauto.
Qed.

Lemma App_typing_spine Gamma1 Gamma2 Gamma m ms A B :
  [ Gamma1 |- m :- A ] ->
  typing_spine Gamma2 A ms B ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma |- spine m ms :- B ].
Proof.
  move=> tyM tsp. elim: tsp Gamma1 Gamma m tyM=>//={Gamma2 A ms B}.
  move=> Gamma2 A B s l p sb tyA Gamma1 Gamma m tyM mg.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_pure2 mg p)=>->.
    apply: s_Conv; eauto.
    rewrite e1. rewrite<-e2. 
    rewrite<-pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l p sb
    tyProd tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Prod_App; eauto.
    apply: s_Conv; eauto.
    rewrite e1'. rewrite<-e2'.
    rewrite<-e1. rewrite<-pure_re; eauto.
    move: (merge_re2 Gamma1').
    rewrite e1'.
    rewrite <-e2'.
    rewrite <-e1.
    rewrite <-pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l sb
    tyProd tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[GammaX[mg1 mg2]].
    move: (merge_re_re mg1)=>[e1 e2].
    apply: ih; eauto.
    apply: l_Prod_App; eauto.
    apply: s_Conv.
    apply: sb.
    2:{ apply: tyM. }
    rewrite e2. rewrite<-e1; eauto.
    apply: merge_sym; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l p sb
    tyLolli tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_pure1 mg p)=>e.
    move: (merge_re_re mg)=>[e1 e2].
    move: (merge_re_re mg')=>[e1' e2'].
    rewrite e in mg'.
    apply: ih; eauto.
    apply: u_Lolli_App; eauto.
    apply: s_Conv; eauto.
    rewrite e1'. rewrite<-e2'.
    rewrite<-e1. rewrite<-pure_re; eauto.
    move: (merge_re2 Gamma1').
    rewrite e1'.
    rewrite <-e2'.
    rewrite <-e1.
    rewrite <-pure_re; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l  sb
    tyLolli tyHd mg tySp ih Gamma1' Gamma2' m tyM mg'.
    move: (merge_sym mg')=>{}mg'.
    move: (merge_merge mg mg')=>[GammaX[mg1 mg2]].
    move: (merge_re_re mg1)=>[e1 e2].
    apply: ih; eauto.
    apply: l_Lolli_App; eauto.
    apply: s_Conv.
    apply: sb.
    2:{ apply: tyM. }
    rewrite e2. rewrite<-e1; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma typing_spine_u_Prod_rcons Gamma1 Gamma2 Gamma A B C n ms :
  typing_spine Gamma1 A ms (Prod B C U) ->
  pure Gamma2 ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Prod B C U)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Prod_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H4 H)=>e1.
    move: (merge_pure2 H4 H2)=>e2.
    destruct s.
    apply: typing_spine_u_Prod_cons; eauto.
      rewrite<-e1. rewrite e2; eauto.
      apply: merge_sym; eauto.
      move: (substitutionU tyC H3 H2 H4)=>//=tyCN.
      apply: typing_spine_nil; eauto.
      rewrite<-e2; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Prod_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma typing_spine_l_Prod_rcons Gamma1 Gamma2 Gamma A B C n ms :
  typing_spine Gamma1 A ms (Prod B C L) ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Prod B C L)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Prod_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H3)=>[e1 e2].
    destruct s.
    apply: typing_spine_l_Prod_cons.
      3:{ apply: H2. }
      apply: H0.
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H2)=>//=tyCN.
      apply: typing_spine_nil; eauto.
    exfalso. apply: sub_Sort_False1; eauto.
  - move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_u_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma typing_spine_u_Lolli_rcons Gamma1 Gamma2 Gamma A B C n ms :
  typing_spine Gamma1 A ms (Lolli B C U) ->
  pure Gamma2 ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C U)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (u_Lolli_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_pure1 H4 H)=>e1.
    move: (merge_pure2 H4 H2)=>e2.
    destruct s.
    exfalso. apply: sub_Sort_False2; eauto.
    apply: typing_spine_u_Lolli_cons; eauto.
      rewrite<-e1. rewrite e2; eauto.
      apply: merge_sym; eauto.
      move: (substitutionU tyC H3 H2 H4)=>//=tyCN.
      apply: typing_spine_nil; eauto.
      rewrite<-e2; eauto.
  - move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Prod_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_pure1 H3 H)=>e1.
    move: (merge_pure2 H8 H6)=>e2.
    subst.
    apply: typing_spine_u_Lolli_cons.
    apply: H.
    apply: H0.
    apply: H1.
    apply: H2.
    apply: H3.
    apply: H5; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma typing_spine_l_Lolli_rcons Gamma1 Gamma2 Gamma A B C n ms :
  typing_spine Gamma1 A ms (Lolli B C L) ->
  [ Gamma2 |- n :- B ] ->
  merge Gamma1 Gamma2 Gamma ->
  typing_spine Gamma A (rcons ms n) C.[n/].
Proof.
  move e:(Lolli B C L)=> T sp.
  elim: sp Gamma2 Gamma B C n e=>{Gamma1 A ms T}; intros; subst.
  - rewrite /rcons.
    move: (l_Lolli_inv H1)=>[s'[l1'[l2'[tyB [tyC sb]]]]].
    move: (merge_re_re H3)=>[e1 e2].
    destruct s.
    exfalso. apply: sub_Sort_False2; eauto.
    apply: typing_spine_l_Lolli_cons.
      3:{ apply: H2. }
      apply: H0.
      rewrite e2. rewrite<-e1.
      rewrite <-pure_re; eauto.
      apply: merge_sym; eauto.
      move: (substitutionN tyC H2)=>//=tyCN.
      apply: typing_spine_nil; eauto.
  - move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_u_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Prod_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H3)=>mg.
    move: (merge_merge mg H7)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: merge_sym; eauto.
  - move: (merge_sym H2)=>mg.
    move: (merge_merge mg H6)=>[Gamma4[mg1 mg2]].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: merge_sym; eauto.
Qed.

Lemma typing_spine_sub Gamma A B C ms s l :
  typing_spine Gamma A ms B ->
  B <: C ->
  [ re Gamma |- C :- s @ l ] ->
  typing_spine Gamma A ms C.
Proof.
  move=>sp. elim: sp C s l=>{Gamma A B ms}.
  move=> Gamma A B s l p sb tyB C s' l' sb' tyC.
    apply: typing_spine_nil; eauto.
    apply: sub_trans; eauto.
    rewrite <-pure_re in tyC; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l p sb
    tyProd tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_u_Prod_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l sb
    tyProd tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_l_Prod_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l p sb
    tyProd tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_u_Lolli_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
  move=> Gamma1 Gamma2 Gamma hd tl T A B B' l sb
    tyProd tyHd mg tySp ih C s l' sb' tyC.
    move: (merge_re_re mg)=>[e1 e2].
    apply: typing_spine_l_Lolli_cons; eauto.
    apply: ih; eauto.
    rewrite e2; eauto.
Qed.

Lemma spine'_inv Gamma m ms B :
  [ Gamma |- ] ->
  [ Gamma |- spine' m ms :- B ] ->
  exists Gamma1 Gamma2 A,
    merge Gamma1 Gamma2 Gamma /\
    [ Gamma1 |- m :- A ] /\
    typing_spine Gamma2 A (rev ms) B.
Proof.
  move e:(spine' m ms)=> n wf ty.
  elim: ty m ms wf e=>{Gamma n B}.
  move=> Gamma s l p m ms wf sp. 
    destruct ms; try discriminate. simpl in sp; subst.
    exists Gamma. exists Gamma. exists (U @ l.+1).
    rewrite /rev/catrev.
    repeat constructor; eauto.
    apply: merge_pure; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Gamma. exists Gamma. exists (U @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: u_Prod; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Gamma. exists Gamma. exists (U @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: l_Prod; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Gamma. exists Gamma. exists (L @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: u_Lolli; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    have e : spine' B nil = B by eauto.
    exists Gamma. exists Gamma. exists (L @ l).
    rewrite /rev/catrev.
    repeat split.
    apply: merge_pure; eauto.
    apply: l_Lolli; eauto.
    apply: typing_spine_nil; eauto.
    apply: u_Sort; eauto.
  move=> Gamma x A h m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    move: (hasU_pure h)=>p.
    move: (hasU_ok wf h)=>[l tyA].
    exists Gamma. exists (re Gamma). exists A.
    repeat split.
    rewrite<- !pure_re; eauto.
    apply: merge_pure; eauto.
    apply: u_Var; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure; eauto.
  move=> Gamma x A h m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    move: (hasL_ok wf h)=>[l tyA].
    exists Gamma. exists (re Gamma). exists A.
    repeat split.
    apply: merge_re2.
    apply: l_Var; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure; eauto.
  move=> Gamma n A B s t l p tyProd ihProd tyN ihN m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    exists Gamma. exists Gamma. exists (Prod A B s).
    repeat split.
    apply: merge_pure; eauto.
    apply: u_Lam; eauto.
    apply: typing_spine_nil; eauto.
  move=> Gamma n A B s t l tyLolli ihLolli tyN ihN m ms wf sp.
    destruct ms; try discriminate. simpl in sp; subst.
    exists Gamma. exists (re Gamma). exists (Lolli A B s).
    repeat split.
    apply: merge_re2.
    apply: l_Lam; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure.
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    subst.
      move: (merge_pure2 mg p)=>e; subst.
      move: (merge_re_re mg)=>[e1 e2].
      move: (u_Prod_App p tyM tyN mg)=>tyApp.
      move: (propagation wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Gamma1. exists Gamma2. exists (B.[n/]).
      repeat split; eauto.
      apply: typing_spine_nil; eauto.
      replace Gamma2 with (re Gamma2).
      rewrite e2; eauto.
      rewrite<-pure_re; eauto.
    inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Gamma3[Gamma4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Gamma5[mg1 mg2]].
      move: (merge_pure2 mg1 p)=>{}e.
      exists Gamma3. exists Gamma5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_u_Prod_rcons; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    subst.
      move: (l_Prod_App tyM tyN mg)=>tyApp.
      move: (propagation wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Gamma. exists (re Gamma). exists (B.[n/]).
      repeat split; eauto.
      apply: merge_re2.
      apply: typing_spine_nil; eauto.
      apply: re_pure.
    inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Gamma3[Gamma4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Gamma5[mg1 mg2]].
      exists Gamma3. exists Gamma5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_l_Prod_rcons; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    subst.
      move: (merge_pure2 mg p)=>e; subst.
      move: (merge_re_re mg)=>[e1 e2].
      move: (u_Lolli_App p tyM tyN mg)=>tyApp.
      move: (propagation wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Gamma1. exists Gamma2. exists (B.[n/]).
      repeat split; eauto.
      apply: typing_spine_nil; eauto.
      replace Gamma2 with (re Gamma2).
      rewrite e2; eauto.
      rewrite<-pure_re; eauto.
    inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Gamma3[Gamma4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Gamma5[mg1 mg2]].
      move: (merge_pure2 mg1 p)=>{}e.
      exists Gamma3. exists Gamma5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_u_Lolli_rcons; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg m' ms wf sp.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    destruct ms; simpl in sp.
    subst.
      move: (l_Lolli_App tyM tyN mg)=>tyApp.
      move: (propagation wf tyApp)=>[s[l tyBN]].
      rewrite /rev/catrev.
      exists Gamma. exists (re Gamma). exists (B.[n/]).
      repeat split; eauto.
      apply: merge_re2.
      apply: typing_spine_nil; eauto.
      apply: re_pure.
    inv sp.
      have e : spine' m' ms = spine' m' ms by eauto.
      move: (ihM m' ms wf1 e)=>[Gamma3[Gamma4[A0[mg'[tyM' tySp]]]]].
      move: (merge_sym mg')=>{}mg'.
      move: (merge_merge mg' mg)=>[Gamma5[mg1 mg2]].
      exists Gamma3. exists Gamma5. exists A0.
      repeat split.
      apply: merge_sym; eauto.
      apply: tyM'.
      rewrite rev_cons.
      apply: typing_spine_l_Lolli_rcons; eauto.
  move=> Gamma A s Cs l a cs p tyA ihA tyCs m ms wf sp.
    destruct ms; simpl in sp; try discriminate; subst.
    rewrite /rev/catrev.
    exists Gamma. exists Gamma. exists A.
    repeat split.
    apply: merge_pure; eauto.
    apply: s_Ind; eauto.
    apply: typing_spine_nil; eauto.
  move=> Gamma A s i C Cs I ig p tyI ihI m ms wf sp.
    destruct ms; simpl in sp; try discriminate; subst.
    move: (s_Ind_inv tyI)=>[l[a[cs[_[tyA tyCs]]]]].
    move: (iget_Forall ig tyCs)=>tyC.
    have mg : merge Gamma Gamma Gamma.
      apply: merge_pure; eauto.
    move: (substitutionU tyC tyI p mg)=>tyCI.
    rewrite /rev/catrev.
    exists Gamma. exists Gamma. exists (C.[I/]).
    repeat split.
    apply: merge_pure; eauto.
    apply: s_Constr; eauto.
    apply: typing_spine_nil; eauto.
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms I a mg
    tyM ihM tyQ ihQ tyFsCs m0 ms0 wf sp.
    destruct ms0; simpl in sp; try discriminate; subst.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].
    have mg' : merge (re Gamma2) (re Gamma1) (re Gamma).
      rewrite e1. rewrite e2. apply: merge_re_re_re.
    move: (propagation wf1 tyM)=>[s0[l tyI]].
    have p : pure (re Gamma1).
      apply: re_pure.
    move: (s_Ind_spine_inv p a tyI)=>[s1[l0 tySp]].
    move: (arity1_spine s' tySp a p)=>{tySp}/arity_typing_spine tySp.
    move: (App_typing_spine tyQ tySp mg')=>{}tySp.
    rewrite /rev/catrev.
    exists Gamma. exists (re Gamma). exists (spine Q ms).
    repeat split; eauto.
    apply: merge_re2.
    apply: s_Case; eauto.
    apply: typing_spine_nil.
    apply: re_pure.
    eauto.
    apply: tySp.
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms I a p mg
    tyM ihM tyQ ihQ tyFsCs m0 ms0 wf sp.
    destruct ms0; simpl in sp; try discriminate; subst.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].      
    have mg' : merge (re Gamma2) (re Gamma1) (re Gamma).
      rewrite e1. rewrite e2. apply: merge_re_re_re.    
    have tyM' : [ re Gamma1 |- m :- spine I ms ].
      rewrite <-pure_re; eauto.
    move: (propagation wf1 tyM)=>[s0[l tyI]].
    have pr : pure (re Gamma1).
      apply: re_pure.
    move: (s_Ind_spine pr tyI)=>tyInd.
    move: (s_Ind_inv tyInd)=>{a}[l0[a[cs[_[tyA tyCs]]]]].
    move: (s_Ind_spine_inv pr a tyI)=>[s1[l1 tySp]].
    move: (arity2_spine s' tySp a pr tyInd)=>{tySp}/arity_typing_spine tySp.
    move: (App_typing_spine tyQ tySp mg')=>{}tySp.
    rewrite <-e2 in tySp.
    move: (u_Prod_App pr tySp tyM' mg')=>tyApp.
    rewrite /rev/catrev.
    exists Gamma. exists (re Gamma). exists (App (spine Q ms) m).
    repeat split; eauto.
    apply: merge_re2.
    apply: s_DCase; eauto.
    rewrite <-pure_re; eauto.
    apply: typing_spine_nil; eauto.
    apply: re_pure.
  move=> Gamma A m l p tyA ihA tyM ihM m0 ms wf sp.
    destruct ms; simpl in sp; try discriminate; subst.
    exists Gamma. exists Gamma. exists A.
    repeat split.
    apply: merge_pure; eauto.
    eapply u_Fix; eauto.
    apply: typing_spine_nil; eauto.
  move=> Gamma A B m s l sb tyB ihB tyM ihM m0 ms wf sp.
    subst.
    have e : (spine' m0 ms = spine' m0 ms) by eauto.
    move: (ihM m0 ms wf e)=>[Gamma1[Gamma2[A0[mg[tyM0 tySp]]]]].
    move: (merge_re_re mg)=>[e1 e2].
    exists Gamma1. exists Gamma2. exists A0.
    repeat split; eauto.
    apply: typing_spine_sub; eauto.
    rewrite e2; eauto.
Qed.

Lemma spine_inv Gamma m ms B :
  [ Gamma |- ] ->
  [ Gamma |- spine m ms :- B ] ->
  exists Gamma1 Gamma2 A,
    merge Gamma1 Gamma2 Gamma /\
    [ Gamma1 |- m :- A ] /\
    typing_spine Gamma2 A ms B.
Proof.
  rewrite spine_spine'_rev=>wf tySp.
  move: (spine'_inv wf tySp)=>[Gamma1[Gamma2[A[mg[tyM sp]]]]].
  rewrite revK in sp.
  exists Gamma1. 
  exists Gamma2.
  exists A.
  eauto.
Qed.

Lemma arity_step s A A' :
  arity s A -> step A A' -> arity s A'.
Proof.
  move=> a. elim: a A'.
  move=> l A' st. inv st.
  move=> A0 B a ih A' st. inv st.
    constructor; eauto.
    constructor; eauto.
Qed.

Definition n_Beta k (sigma : var -> term) x :=
  k < x.+1 /\
  (forall i, i < k -> sigma i = (Var i)) /\
  (noccurs x (sigma k)) /\
  (forall i, k < i -> (sigma i).[ren (+1)] = Var i).

Lemma noccurs_n_Beta x m :
  noccurs x m -> n_Beta 0 (m .: ids) x.
Proof.
  move=> no.
  firstorder.
  inv H.
  destruct i.
  inv H.
  asimpl; eauto.
Qed.

Lemma n_Beta_up k x sigma :
  n_Beta k sigma x -> n_Beta k.+1 (up sigma) x.+1.
Proof.
  move=> [lt[h1[h2 h3]]].
  firstorder.
  destruct i; asimpl; eauto.
    have lt' : i < k by eauto.
    replace (Var i.+1) with (Var i).[ren (+1)] by eauto.
    f_equal; eauto.
  asimpl.
    apply noccurs_up; eauto.
  destruct i.
    inv H.
    have lt' : k < i by eauto.
    move: (h3 _ lt')=>e; asimpl.
    replace (sigma i).[ren (+2)] 
      with (sigma i).[ren (+1)].[ren (+1)] by autosubst.
    rewrite e; eauto.
Qed.

Lemma lt_False x y : x < y -> y < x.+1 -> False.
Proof.
  elim: x y; intros.
  destruct y.
  inv H.
  inv H0.
  destruct y.
  inv H0.
  eapply H; eauto.
Qed.

Lemma noccurs_Beta k x m sigma :
  noccurs (x.+1) m -> n_Beta k sigma x -> noccurs x m.[sigma].
Proof with eauto using n_Beta_up, lt_False.
  move e:(x.+1)=> i no. move: i m no sigma k x e. 
  apply: noccurs_ind_nested=>//=; intros; subst; try constructor...
  unfold n_Beta in H0; firstorder.
    move: (ltngtP k y)=>[h|h|h].
    move: (H3 _ h)=>e.
    destruct (sigma y); try discriminate.
    inv e.
    constructor; eauto.
    rewrite H1; eauto.
    constructor.
    intro; subst...
    subst; eauto.
  elim: H2=>//=; intros.
    constructor...
  elim: H4=>//=; intros.
    constructor...
  elim: H4=>//=; intros.
    constructor...
Qed.

Lemma noccurs_spine' x h1 h2 ms : 
  noccurs x (spine' h1 ms) -> noccurs x h2 -> noccurs x (spine' h2 ms).
Proof.
  move e:(spine' h1 ms)=> n no. move: x n no h1 h2 ms e.
  apply: noccurs_ind_nested; intros;
  match goal with
  | [ H : spine' _ ?ms = _ |- _ ] =>
    destruct ms; simpl; simpl in H; inv H; eauto
  end.
  constructor; eauto.
Qed.

Lemma noccurs_spine x h1 h2 ms : 
  noccurs x (spine h1 ms) -> noccurs x h2 -> noccurs x (spine h2 ms).
Proof.
  rewrite! spine_spine'_rev=> noSp no.
  apply: noccurs_spine'; eauto.
Qed.

Lemma noccurs_step x m n :
  noccurs x m -> step m n -> noccurs x n.
Proof with eauto using noccurs, noccurs_Beta, noccurs_n_Beta.
  move=> no. move: x m no n. 
  apply: noccurs_ind_nested; intros;
  match goal with
  | [ H : step _ _ |- _ ] => 
    try solve [inv H; eauto using noccurs]
  end.
  inv H3.
    move: (H0 _ H7)=>no...
    move: (H2 _ H7)=>no...
    inv H...
  inv H3...
    constructor...
    elim: H8 H2 H1=>//=; intros.
      inv H2. inv H3. constructor...
      inv H3. inv H4. constructor...
  inv H5...
    constructor...
      elim: H10 H4 H3=>//=; intros.
        inv H4. inv H5. constructor...
        inv H5. inv H6. constructor...
    apply: noccurs_spine; eauto.
      elim: H10 H3; intros.
        inv H3...
        inv H6...
  inv H5...
    constructor...
      elim: H10 H4 H3=>//=; intros.
        inv H4. inv H5. constructor...
        inv H5. inv H6. constructor...
    apply: noccurs_spine; eauto.
      elim: H10 H3; intros.
        inv H3...
        inv H6...
  inv H3...
Qed.

Lemma head_spine'_step h h' ms :
  step h h' -> step (spine' h ms) (spine' h' ms).
Proof.
  elim: ms h h'; eauto.
  move=> h ms ih h1 h2 st; simpl.
  constructor; eauto.
Qed.

Lemma head_spine_step h h' ms :
  step h h' -> step (spine h ms) (spine h' ms).
Proof.
  rewrite! spine_spine'_rev=>st.
  apply: head_spine'_step; eauto.
Qed.

Lemma Var_spine'_step x ms C :
  step (spine' (Var x) ms) C ->
  List.Forall (noccurs x) ms ->
  exists ms', 
    C = spine' (Var x) ms' /\ List.Forall (noccurs x) ms'.
Proof.
  elim: ms x C=>//=.
  move=> x C st. inv st.
  move=> a l ih x C st no.
    inv no.
    inv st.
    move: (ih x m' H4 H2)=>[ms'[e no]]; subst.
      exists (a :: ms'); eauto.
    exists (n' :: l); firstorder.
      constructor; eauto.
      apply: noccurs_step; eauto.
    destruct l; inv H0.
Qed.

Lemma noccurs_Forall_cat x ms ns :
  List.Forall (noccurs x) ms ->
  List.Forall (noccurs x) ns ->
  List.Forall (noccurs x) (ms ++ ns).
Proof with eauto using List.Forall.
  move=> no. elim: no ns=>//={ms}...
Qed.

Lemma noccurs_Forall_rev x ms :
  List.Forall (noccurs x) ms -> List.Forall (noccurs x) (rev ms).
Proof with eauto using List.Forall.
  elim: ms=>//=; intros.
  inv H0.
  move: (H H4)=> {}H.
  replace (a :: l) with ([:: a] ++ l) by eauto.
  rewrite rev_cat.
  apply: noccurs_Forall_cat; eauto.
  rewrite /rev/catrev...
Qed.

Lemma Var_spine_step x ms C :
  step (spine (Var x) ms) C ->
  List.Forall (noccurs x) ms ->
  exists ms', 
    C = spine (Var x) ms' /\ List.Forall (noccurs x) ms'.
Proof.
  rewrite! spine_spine'_rev.
  move=> st /noccurs_Forall_rev no.
  move: (Var_spine'_step st no)=>[ms' [h1 h2]].
  exists (rev ms'). split.
  rewrite spine_spine'_rev. rewrite revK; eauto.
  apply noccurs_Forall_rev; eauto.
Qed.

Lemma pos_step x A B :
  pos x A -> step A B -> pos x B.
Proof.
  move=> p. elim: p B=>{A x}.
  move=> x ms no B st.
    move: (Var_spine_step st no)=>[ms'[e no']]; subst.
    constructor; eauto.
  move=> x A B s n p ih B' st. inv st.
    constructor; eauto.
    apply: noccurs_step; eauto.
    constructor; eauto.
  move=> x A B s n p ih B' st. inv st.
    constructor; eauto.
    apply: noccurs_step; eauto.
    constructor; eauto.
Qed.

Lemma active_step x C C' :
  active x C -> step C C' -> active x C'.
Proof.
  move=> a. elim: a C'=>{C x}.
  move=> x ms no C' st.
    move: (Var_spine_step st no)=>[ms'[e no']]; subst.
    apply: active_X; eauto.
  move=> x A B s p a ih no C' st. inv st.
    apply: active_Pos; eauto.
    apply: pos_step; eauto.
    apply: active_Pos; eauto.
    apply: noccurs_step; eauto.
  move=> x A B s n a ih C' st. inv st.
    apply: active_Lolli; eauto.
    apply: noccurs_step; eauto.
    apply: active_Lolli; eauto.
Qed.

Lemma constr_step x s C C' :
  constr x s C -> step C C' -> constr x s C'.
Proof.
  move=> c. elim: c C'=>{C x s}.
  move=> x s ms no C' st.
    move: (Var_spine_step st no)=>[ms'[e no']]; subst.
    apply: constr_X; eauto.
  move=> x A B p c ih no C' st. inv st.
    apply: constr_UPos; eauto.
    apply: pos_step; eauto.
    apply: constr_UPos; eauto.
    apply: noccurs_step; eauto.
  move=> x A B n c ih C' st. inv st.
    apply: constr_UProd; eauto.
    apply: noccurs_step; eauto.
    apply: constr_UProd; eauto.
  move=> x A B p c ih n C' st. inv st.
    apply: constr_LPos1; eauto.
    apply: pos_step; eauto.
    apply: constr_LPos1; eauto.
    apply: noccurs_step; eauto.
  move=> x A B p a n C' st. inv st.
    apply: constr_LPos2; eauto.
    apply: pos_step; eauto.
    apply: constr_LPos2; eauto.
    apply: active_step; eauto.
    apply: noccurs_step; eauto.
  move=> x A B n c ih C' st. inv st.
    apply: constr_LProd1; eauto.
    apply: noccurs_step; eauto.
    apply: constr_LProd1; eauto.
  move=> x A B n a C' st. inv st.
    apply: constr_LProd2; eauto.
    apply: noccurs_step; eauto.
    apply: constr_LProd2; eauto.
    apply: active_step; eauto.
Qed.

Lemma iget_step i Cs Cs' C :
  iget i Cs C -> One2 step Cs Cs' -> 
    exists C', C === C' /\ iget i Cs' C'.
Proof.
  move=> ig h. elim: h i ig=>{Cs Cs'}.
  move=> m m' Cs st i ig. inv ig.
    exists m'. split.
      apply: conv1; eauto.
      constructor.
    exists C. split; eauto.
      constructor; eauto.
  move=> m Cs Cs' h ih i ig. inv ig.
    exists C. repeat constructor.
    move: (ih _ H3)=>[C' [e ig]].
    exists C'. repeat constructor; eauto.
Qed.

Lemma respine_step Q Q' C :
  step Q Q' -> step (respine Q C) (respine Q' C).
Proof.
  elim: C Q Q'=>//=.
  move=> A ihA B ihB s Q Q' st.
    constructor.
    apply: ihB.
    apply: step_subst; eauto.
  move=> A ihA B ihB s Q Q' st.
    constructor.
    apply: ihB.
    apply: step_subst; eauto.
  move=> m ihM n ihN Q Q' st.
    constructor; eauto.
Qed.

Lemma case_step I Q Q' C :
  step Q Q' -> step (case I Q C) (case I Q' C).
Proof.
  move=>st. unfold case.
  apply: respine_step; eauto.
Qed.

Lemma respine_spine'_Ind Q A Cs s ms :
  respine Q (spine' (Ind A Cs s) ms) = spine' Q ms.
Proof.
  elim: ms; simpl; intros; eauto.
  rewrite H; eauto.
Qed.

Lemma respine_spine_Ind Q A Cs s ms :
  respine Q (spine (Ind A Cs s) ms) = spine Q ms.
Proof.
  rewrite! spine_spine'_rev.
  apply: respine_spine'_Ind.
Qed.

Lemma spine'_Var x y ms :
  spine' (Var x) ms = Var y -> x = y /\ ms = nil.
Proof.
  elim: ms; simpl; intros.
  inv H; eauto.
  inv H0.
Qed.

Lemma app_False (ls : list term) x :
  ls ++ [:: x] = nil -> False.
Proof.
  elim: ls; simpl; intros.
  inv H.
  inv H0.
Qed.

Lemma rev_nil (ls : list term) :
  rev ls = nil -> ls = nil.
Proof.
  destruct ls; eauto.
  replace (t :: ls) with ([:: t] ++ ls) by eauto.
  rewrite rev_cat.
  rewrite /rev/catrev=>h.
  exfalso.
  apply: app_False; eauto.
Qed.

Lemma spine_Var x y ms :
  spine (Var x) ms = Var y -> x = y /\ ms = nil.
Proof.
  rewrite spine_spine'_rev=> /spine'_Var[-> e].
  firstorder.
  apply: rev_nil; eauto.
Qed.

Lemma has_type_Lam_False Gamma A B C s l :
  [ Gamma |- Lam A B U :- C ] -> C <: s @ l -> False.
Proof.
  move e1:(Lam A B U)=> m ty.
  move: Gamma m C ty A B s l e1.
  apply: has_type_nested_ind; intros; 
  try (discriminate || solve[exfalso; solve_sub]).
  subst.
  apply: H3; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma has_type_Ind_False Gamma X Cs A B C r s t l :
  [ Gamma |- Ind X Cs s :- C ] -> C <: Prod A B r ->
  [ Gamma |- Ind X Cs s :- t @ l ] -> False.
Proof.
  move e:(Ind X Cs s)=>I ty.
  move: Gamma I C ty X Cs A B r s t l e.
  apply: has_type_nested_ind; try discriminate; intros.
  - inv e.
    apply s_Ind_invX in H7. firstorder.
    inv H8.
    clear H7.
    exfalso; solve_sub.
    clear H6.
    exfalso; solve_sub.
  - subst.
    apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Ltac solve_spine' :=
  match goal with
  | [ H : spine' _ ?ms = _ |- ?x ] =>
    destruct ms; simpl in H; intros;
    match goal with
    | [ H : _ = ?x |- _ ] => inv H
    end
  | [ H : _ = spine' _ ?ms |- ?x ] =>
    destruct ms; simpl in H; intros;
    match goal with
    | [ H : ?x = _ |- _ ] => inv H
    end
  end.

Ltac solve_spine :=
  match goal with
  | [ H : spine _ _ = _ |- _ ] =>
    rewrite spine_spine'_rev in H; solve_spine'
  | [ H : _ = spine _ _ |- _ ] =>
    rewrite spine_spine'_rev in H; solve_spine'
  end.

Lemma active_respine Gamma I Cs A Q C n r s t l :
  active n C ->
  arity s A ->
  (forall i Q, respine Q (I i) = Q) ->
  (I n = Ind A Cs s) ->
  [ re Gamma |- I n :- A ] ->
  [ re Gamma |- Q :- arity1 t A ] ->
  [ re Gamma |- C.[I] :- r @ l ] ->
  exists s l,
    [ re Gamma |- respine Q C.[I] :- s @ l ].
Proof.
  elim: C Gamma I Cs A Q n r s t l; simpl; intros;
  match goal with
  | [ H : active _ _ |- _ ] => 
    try solve [inv H; exfalso; solve_spine]
  end.
  - inv H.
    move: (spine_Var H6)=>[e _]; subst. inv H0.
    + exists t. exists l0. rewrite H1; eauto.
    + rewrite H2 in H3. 
      rewrite H2 in H5.
      exfalso.
      apply: has_type_Ind_False.
      apply: H3.
      eauto.
      apply: H5.
  - specialize
    (@H0 (A.[I] +{s} Gamma) (up I) 
      Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] n.+1).
    inv H1; try solve[exfalso; solve_spine]; destruct s. 
    move: (u_Lolli_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H4. autosubst.
      have h4 : [ A.[I] +u re Gamma |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningU; eauto.
      have h5 : [ A.[I] +u re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H13 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure.
    move: (l_Lolli_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H4. autosubst.
      have h4 : [ +n re Gamma |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningN; eauto.
      have h5 : [ +n re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H13 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure.
    move: (u_Lolli_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H4. autosubst.
      have h4 : [ A.[I] +u re Gamma |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningU; eauto.
      have h5 : [ A.[I] +u re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H13 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure.
    move: (l_Lolli_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H4. autosubst.
      have h4 : [ +n re Gamma |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningN; eauto.
      have h5 : [ +n re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H13 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure.
  - inv H1.
    replace (App (respine Q m.[I]) n.[I]) 
      with (respine Q (App m n).[I]) by eauto.
    replace (App m.[I] n.[I]) with (App m n).[I] in H7 by eauto.
    rewrite <-H8.
    rewrite <-H8 in H7.
    rewrite spine_subst; simpl.
    rewrite spine_subst in H7; simpl in H7.
    rewrite H4.
    rewrite H4 in H7.
    have p : pure (re Gamma).
      apply: re_pure.
    move: (s_Ind_spine_inv p H2 H7)=>[s0[l0 tySp]].
    move: (arity1_spine t tySp H2 p)=>{}tySp.
    move: (merge_re_re_re Gamma)=>mg.
    move: (App_arity_spine H6 tySp mg)=>tyQ.
    rewrite respine_spine_Ind.
    exists t. exists l0; eauto.
Qed.

Lemma constr_respine Gamma I Cs A Q C n r s t l :
  constr n s C ->
  arity s A ->
  (forall i Q, respine Q (I i) = Q) ->
  (I n = Ind A Cs s) ->
  [ re Gamma |- I n :- A ] ->
  [ re Gamma |- Q :- arity1 t A ] ->
  [ re Gamma |- C.[I] :- r @ l ] ->
  exists s l,
    [ re Gamma |- respine Q C.[I] :- s @ l ].
Proof.
  elim: C Gamma I Cs A Q n r s t l; simpl; intros;
  match goal with
  | [ H : constr _ _ _ |- _ ] => 
    try solve [inv H; exfalso; solve_spine]
  end.
  - inv H.
    move: (spine_Var H6)=>[e _]; subst. inv H0.
    + exists t. exists l0. rewrite H1; eauto.
    + rewrite H2 in H3.
      rewrite H2 in H5. 
      exfalso. 
      apply: has_type_Ind_False.
      apply: H3.
      eauto.
      apply: H5.
  - specialize (@H0 (A.[I] +{s} Gamma) (up I) 
      Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] n.+1).
    inv H1; try solve[exfalso; solve_spine].
    move: (u_Prod_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity U A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U).
        asimpl. rewrite H4. autosubst.
      have h4 : [A.[I] +u re Gamma |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h5 : [A.[I] +u re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' U t l1 H14 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure.
    move: (u_Prod_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity U A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U).
        asimpl. rewrite H4. autosubst.
      have h4 : [A.[I] +u re Gamma |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h5 : [A.[I] +u re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' U t l1 H14 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure.
    move: (u_Prod_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H4. autosubst.
      have h4 : [A.[I] +u re Gamma |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h5 : [A.[I] +u re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' L t l1 H14 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure.
    move: (l_Prod_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H4. autosubst.
      have h4 : [ re (A.[I] +l Gamma) |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningN; eauto.
      have h5 : [ re (A.[I] +l Gamma) |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (active_respine H14 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure.
    move: (u_Prod_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H4. autosubst.
      have h4 : [A.[I] +u re Gamma |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h5 : [A.[I] +u re Gamma |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' L t l1 H14 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure.
    move: (l_Prod_inv H7)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (forall i Q, respine Q (up I i) = Q).
        apply: respine_up; eauto.
      have h3 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H4. autosubst.
      have h4 : [ re (A.[I] +l Gamma) |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningN; eauto.
      have h5 : [ re (A.[I] +l Gamma) |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (active_respine H14 h1 h2 h3 h4 h5 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure.
  - inv H1.
    replace (App (respine Q m.[I]) n.[I])
      with (respine Q (App m n).[I]) by eauto.
    replace (App m.[I] n.[I]) with (App m n).[I] in H7 by eauto.
    rewrite <- H8.
    rewrite <- H8 in H7.
    rewrite spine_subst; simpl.
    rewrite spine_subst in H7; simpl in H7.
    rewrite H4.
    rewrite H4 in H7.
    have p : pure (re Gamma).
      apply: re_pure.
    move: (s_Ind_spine_inv p H2 H7)=>[s0[l0 tySp]].
    move: (arity1_spine t tySp H2 p)=>{}tySp.
    move: (merge_re_re_re Gamma)=> mg.
    move: (App_arity_spine H6 tySp mg)=>tyQ.
    rewrite respine_spine_Ind.
    exists t. exists l0; eauto.
Qed.

Lemma All2_case_stepQ Gamma A Q Q' Fs Cs Cs' s t l :
  let I := Ind A Cs' s in
  step Q Q' ->
  arity s A ->
  [ re Gamma |- Ind A Cs' s :- A ] ->
  [ re Gamma |- Q' :- arity1 t A ] ->
  All2 (fun F C => constr 0 s C /\ 
    [ Gamma |- F :- case I Q C ]) Fs Cs ->
  List.Forall (fun C => [ A +u re Gamma |- C :- U @ l ]) Cs ->
  All2 (fun F C => constr 0 s C /\
    [ Gamma |- F :- case I Q' C ]) Fs Cs.
Proof.
  move=> I st a tyInd tyQ all. elim: all=>{Fs Cs}.
  constructor.
  move=> F C Fs Cs [c tyF] hd tl h.
  inv h.
  constructor; eauto.
  firstorder.
  have h1 : (forall i Q, respine Q ((I .: ids) i) = Q).
    destruct i; simpl; eauto.
  have h2 : (I .: ids) 0 = Ind A Cs' s by eauto.
  have h3 : [re Gamma |- C.[I/] :- (U @ l).[I/]].
    apply: substitutionU; eauto.
    apply: re_pure.
    apply: merge_re_re_re.
  have h4 : respine Q C.[I/] <: respine Q' C.[I/].
    apply: conv_sub.
    apply: conv1.
    apply: respine_step; eauto.
  move: 
  (@constr_respine Gamma (I .: ids) Cs' A Q' C 0 U s t l c a h1 h2 
    tyInd tyQ h3)=>[s0[l0 tySp]].
  unfold case.
  unfold case in tyF.
  apply: s_Conv.
  apply: h4.
  apply: tySp.
  apply: tyF.
Qed.

Lemma All2_One2_stepF Gamma A Q Fs Fs' Cs Cs' s :
  let I := Ind A Cs' s in
  [ Gamma |- ] ->
  One2 step Fs Fs' ->
  All2 (fun F C => constr 0 s C /\ 
    [ Gamma |- F :- case I Q C ]) Fs Cs ->
  All2 (fun F C => constr 0 s C /\ ([ Gamma |- ] -> 
    forall F', step F F' -> [ Gamma |- F' :- case I Q C ])) Fs Cs ->
  All2 (fun F C => constr 0 s C /\
    [ Gamma |- F :- case I Q C ]) Fs' Cs.
Proof.
  move=> I wf one. elim: one Cs=>{Fs Fs'}.
  move=> F F' Fs' st Cs hd tl.
    inv hd. inv tl.
    constructor; eauto.
    constructor; firstorder; eauto.
  move=> F Fs Fs' one ih Cs hd tl.
    inv hd. inv tl.
    constructor; eauto.
Qed.

(* Lemma s_Constr_spine'_False Gamma A B C U i m ms :
  [ Gamma |- spine' (Constr i m) ms :- C ] -> 
  Prod A B U <: C -> False.
Proof.

Lemma s_Constr_spine' Gamma A C Cs i m ms1 ms2 s :
  iget i Cs C ->
  [ Gamma |- spine' (Constr i m) ms1 :- spine' (Ind A Cs s) ms2 ] ->
  [ Gamma |- Constr i m :- C.[Ind A Cs s/] ].
Proof.
  move e1:(spine' (Constr i m) ms1)=> n1.
  move e2:(spine' (Ind A Cs s) ms2)=> n2 ig ty.
  elim: ty A C Cs s i m ms1 ms2 ig e1 e2=>{Gamma n1 n2}; intros;
  try solve 
  [ (destruct ms1; simpl in e1; try inv e1) ||
    (destruct ms2; simpl in e2; try inv e2) ].
  - destruct ms1; simpl in e1; inv e1.
    destruct ms2; simpl in e2.
    move: (merge_re_re H4)=>{e2}[<- e2].
    apply: H1; eauto. *)

(* Lemma spine_Constr Gamma A Cs i m ms1 ms2 s :
  let I := Ind A Cs s in
  [ Gamma |- spine (Constr i m) ms1 :- spine I ms2 ] ->
  [ Gamma |- spine (Constr i I) ms1 :- spine I ms2 ].
Proof.
  move=> I.
  rewrite! spine_spine'_rev.
  rewrite! spine_spine'_rev. *)

Theorem subject_reduction Gamma m A :
  [ Gamma |- ] ->
  [ Gamma |- m :- A ] ->
  forall n, step m n -> [ Gamma |- n :- A ].
Proof.
  move=> wf ty.
  move: Gamma m A ty wf. apply: has_type_nested_ind.
  move=> Gamma s l p wf n st. inv st.
  move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: u_Prod; eauto.
      apply: context_convU.
      apply: e.
      rewrite <- pure_re; eauto.
      apply: tyB.
    have {}wf : [ A +u Gamma |- ].
      apply: u_ok; eauto.
      rewrite <- pure_re; eauto.
      move: (ihB wf _ H3)=>tyB'.
      apply: u_Prod; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: l_Prod; eauto.
    have {}wf : [ +n Gamma |- ].
      apply: n_ok; eauto.
      move: (ihB wf _ H3)=>tyB'.
      apply: l_Prod; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: u_Lolli; eauto.
      apply: context_convU.
      apply: e.
      rewrite <- pure_re; eauto.
      apply: tyB.
    have {}wf : [ A +u Gamma |- ].
      apply: u_ok; eauto.
      rewrite <- pure_re; eauto.
      apply: u_Lolli; eauto.
  move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: l_Lolli; eauto.
    have {}wf : [ +n Gamma |- ].
      apply: n_ok; eauto.
      move: (ihB wf _ H3)=>tyB'.
      apply: l_Lolli; eauto.
  move=> Gamma x A hA wf n st. inv st.
  move=> Gamma x A hA wf n st. inv st.
  move=> Gamma n A B s t l p tyProd ihProd tyN ihN wf n' st. inv st.
    have stProd : step (Prod A B s) (Prod A' B s).
      by constructor.
      move: (ihProd wf _ stProd)=>tyProd'.
      apply: s_Conv.
        apply: conv_sub. 
        apply: conv_sym. 
        apply: conv1; eauto.
        rewrite <- pure_re; eauto.
      apply: u_Lam; eauto.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      destruct s.
        move: tyProd=>/u_Prod_inv[_[lA[_[tyA _]]]].
          apply: context_convU.
          apply: e.
          rewrite <- pure_re; eauto.
          apply: tyN.
        move: tyProd=>/l_Prod_inv[_[lA[_[tyA _]]]].
          apply: context_convL.
          apply: e.
          rewrite <- pure_re; eauto.
          apply: tyN.
    destruct s.
      move: (u_Prod_inv tyProd)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A +u Gamma |- ].
          apply: u_ok; eauto.
          rewrite <- pure_re; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: u_Lam; eauto.
      move: (l_Prod_inv tyProd)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A+l Gamma |- ].
          apply: l_ok; eauto.
          rewrite <- pure_re; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: u_Lam; eauto.
  move=> Gamma n A B s t l tyLolli ihLolli tyN ihN wf n' st. inv st.
    have stLolli : step (Lolli A B s) (Lolli A' B s).
      by constructor.
      have {}wf : [ re Gamma |- ].
        apply: re_ok; eauto.
      move: (ihLolli wf _ stLolli)=>tyLolli'.
      apply: s_Conv.
        apply: conv_sub.
        apply: conv_sym.
        apply: conv1; eauto.
        apply: tyLolli.
      apply: l_Lam; eauto.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      destruct s.
        move: tyLolli=>/u_Lolli_inv[_[lA[_[tyA _]]]].
          apply: context_convU.
          apply: e.
          apply: tyA.
          apply: tyN.
        move: tyLolli=>/l_Lolli_inv[_[lA[_[tyA _]]]].
          apply: context_convL.
          apply: e.
          apply: tyA.
          apply: tyN.
    destruct s.
      move: (u_Lolli_inv tyLolli)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A +u Gamma |- ].
          apply: u_ok; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: l_Lam; eauto.
      move: (l_Lolli_inv tyLolli)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A +l Gamma |- ].
          apply: l_ok; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: l_Lam; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (pure_re p)=> e3.
    move: (propagation wf1 tyM)=>[s[l tyProd]].
    inv st.
      move: (ihM _ H2)=>{H2}ihM.
        apply: u_Prod_App; eauto.
      move: (ihN _ H2)=>{}ihN.
        move: (u_Prod_inv tyProd)=>[sB[lB[_ [_ [tyB _]]]]].
        have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
          apply: substitutionU; eauto.
          rewrite e3 e2 e1.
          apply: merge_re_re_re.
        have e : B.[n'0/] === B.[n/].
          apply: conv_Beta.
          apply: conv_sym.
          apply: conv1; eauto.
        apply: s_Conv.
        apply: conv_sub.
        apply: e.
        rewrite <- e1; eauto.
        apply: u_Prod_App; eauto.
      move: (u_Lam_inv tyProd tyM)=>tyM0.
        apply: substitutionU; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (propagation wf1 tyM)=>[s[l tyProd]].
    inv st.
      move: (ihM _ H2)=>{H2}ihM.
        apply: l_Prod_App; eauto.
      move: (ihN _ H2)=>{}ihN.
        move: (l_Prod_inv tyProd)=>[sB[lB[_ [_ [tyB _]]]]].
        have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
          apply: substitutionN; eauto.
        have e : B.[n'0/] === B.[n/].
          apply: conv_Beta.
          apply: conv_sym.
          apply: conv1; eauto.
        apply: s_Conv.
        apply: conv_sub.
        apply: e.
        rewrite <- e1; eauto.
        apply: l_Prod_App; eauto.
      move: (u_Lam_inv tyProd tyM)=>tyM0.
        apply: substitutionL; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (pure_re p)=> e3.
    move: (propagation wf1 tyM)=>[s[l tyLolli]].
    inv st.
      move: (ihM _ H2)=>{H2}ihM.
        apply: u_Lolli_App; eauto.
      move: (ihN _ H2)=>{}ihN.
        move: (u_Lolli_inv tyLolli)=>[sB[lB[_ [_ [tyB _]]]]].
        have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
          apply: substitutionU; eauto.
          rewrite e3 e2 e1.
          apply: merge_re_re_re.
        have e : B.[n'0/] === B.[n/].
          apply: conv_Beta.
          apply: conv_sym.
          apply: conv1; eauto.
        apply: s_Conv.
        apply: conv_sub.
        apply: e.
        rewrite <- e1; eauto.
        apply: u_Lolli_App; eauto.
      move: (l_Lam_inv tyLolli tyM)=>tyM0.
        apply: substitutionU; eauto.
  move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (propagation wf1 tyM)=>[s[l tyLolli]].
    inv st.
      move: (ihM _ H2)=>{H2}ihM.
        apply: l_Lolli_App; eauto.
      move: (ihN _ H2)=>{}ihN.
        move: (l_Lolli_inv tyLolli)=>[sB[lB[_ [_ [tyB _]]]]].
        have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
          apply: substitutionN; eauto.
        have e : B.[n'0/] === B.[n/].
          apply: conv_Beta.
          apply: conv_sym.
          apply: conv1; eauto.
        apply: s_Conv.
        apply: conv_sub.
        apply: e.
        rewrite <- e1; eauto.
        apply: l_Lolli_App; eauto.
      move: (l_Lam_inv tyLolli tyM)=>tyM0.
        apply: substitutionL; eauto.
  move=> Gamma A s Cs l a cs p tyA ihA tyCs ihCs wf n st. inv st.
    move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: e.
      rewrite <- pure_re; eauto.
      apply: s_Ind; eauto.
      apply: arity_step; eauto.
      elim: tyCs=>//=; intros.
        constructor; eauto.
        apply: context_convU.
        apply: e.
        rewrite <- pure_re; eauto.
        apply: H.
    apply: s_Ind; eauto.
      elim: H3 cs; intros.
        inv cs. constructor; eauto.
          apply: constr_step; eauto.
        inv cs. constructor; eauto.
      elim: H3 tyCs ihCs; intros.
        inv tyCs. inv ihCs. constructor; eauto.
          apply: H4; eauto. apply: u_ok; eauto. rewrite <- pure_re; eauto.
        inv tyCs. inv ihCs. constructor; eauto. 
  move=> Gamma A s i C Cs I ig p tyI ihI wf n st. inv st. inv H2.
    - have st : step (Ind A Cs s) (Ind A' Cs s).
        constructor; eauto.
      have e : Ind A' Cs s === Ind A Cs s.
        apply: conv_sym. apply: conv1; eauto.
      move: (ihI wf _ st)=>ihI'.
      move: (s_Ind_inv tyI)=>[l[a[cs[_[tyA tyCs]]]]].
      move: (s_Ind_invX ihI')=>[l'[_[_[_[_[tyA' _]]]]]].
      move: (iget_Forall ig tyCs)=>tyC.
      have mg : merge Gamma Gamma Gamma.
        apply: merge_pure; eauto.
      move: (substitutionU tyC tyI p mg)=>tyCI.
      apply: s_Conv.
      apply: conv_sub. apply: conv_Beta. apply: e.
      rewrite <- pure_re; eauto.
      constructor; eauto.
      apply: s_Conv. apply: conv_sub. apply: conv1; eauto.
      rewrite <- pure_re; eauto.
      apply: ihI'.
    - have st : step (Ind A Cs s) (Ind A Cs' s).
        constructor; eauto.
      have e : Ind A Cs' s === Ind A Cs s.
        apply: conv_sym. apply: conv1; eauto.
      move: (ihI wf _ st)=>ihI'.
      move: (s_Ind_inv tyI)=>[l[a[cs[_[tyA tyCs]]]]].
      move: (s_Ind_inv ihI')=>[l'[_[cs'[_[tyA' tyCs']]]]].
      move: (iget_step ig H4)=>[C' [e' ig']].
      move: (iget_Forall ig tyCs)=>tyC.
      move: (iget_Forall ig' tyCs')=>tyC'.
      have mg : merge Gamma Gamma Gamma.
        apply: merge_pure; eauto.
      move: (substitutionU tyC tyI p mg)=>//=tyCI.
      move: (substitutionU tyC' ihI' p mg)=>//=tyCI'.
      have ex : C.[Ind A Cs s/] === C'.[Ind A Cs' s/].
        apply: (conv_trans C.[Ind A Cs' s/]).
        apply: conv_Beta. apply: conv_sym; eauto.
        apply: conv_subst; eauto.
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply: ex.
      rewrite <- pure_re; eauto.
      constructor; eauto.
  move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms I a mg 
    tyM ihM tyQ ihQ tyFsCs ihFsCs wf n st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].
    move: (propagation wf1 tyM)=>[sI[lI tyI]].
    inv st.
    - move: (ihM wf1 _ H3)=>{}ihM.
      econstructor; eauto.
    - move: (re_ok wf2)=>rwf2.
      move: (ihQ rwf2 _ H3)=>{}ihQ.
      have p : pure (re Gamma1).
        apply: re_pure.
      move: (s_Ind_spine_inv p a tyI)=>[sA[lA sp]].
      move: (@arity1_spine (re Gamma1) ms A sA s s' lA sp a p)=>{}sp.
      rewrite e2 in tyQ. rewrite <- e1 in tyQ.
      rewrite e2 in ihQ. rewrite <- e1 in ihQ.
      move: (merge_re_re_re Gamma1)=>mg1.
      move: (App_arity_spine tyQ sp mg1)=>tySp.
      move: (App_arity_spine ihQ sp mg1)=>tySp'.
      have e : step (spine Q ms) (spine Q' ms).
        apply: head_spine_step; eauto.
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply: conv1; eauto.
      rewrite <-e1; eauto.
      econstructor; eauto.
      rewrite e2. rewrite <-e1; eauto.
      move: (s_Ind_spine p tyI)=>tyInd.
      move: (s_Ind_inv tyInd)=>[l[_[cs[_[tyA tyCs]]]]].
      apply: All2_case_stepQ; eauto.
      rewrite e2; rewrite <-e1; eauto.
      rewrite e2; rewrite <-e1; eauto.
      rewrite e2; rewrite <-e1; eauto.
    - econstructor; eauto.
      apply: All2_One2_stepF; eauto.
    - have p : pure (re Gamma1).
        apply: re_pure.
      move: (s_Ind_spine p tyI)=>tyInd.
