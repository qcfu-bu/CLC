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
| Prod   (A B : term) (s : sort)
| Lolli  (A B : term) (s : sort)
| Lam    (m : term)
| App    (m n : term)
| Ind    (A : term) (s : sort) (Cs : terms)
| Constr (i : nat) (m : term)
| Case   (m Q : term) (Fs : terms)
| DCase  (m Q : term) (Fs : terms)
| Fix    (m : term)

with terms : Type :=
| Nil : terms
| Cons : term -> terms -> terms.

Definition ids_term (v : var) : term := Var v.

Instance Ids_term : Ids term. by apply: ids_term. Defined.

Fixpoint rename_term (xi : var -> var) (t : term) : term :=
  match t with
  | Var x => Var (xi x)
  | Sort s l => Sort s l
  | Prod A B s => Prod (rename_term xi A) (rename_term (upren xi) B) s
  | Lolli A B s => Lolli (rename_term xi A) (rename_term (upren xi) B) s
  | Lam m => Lam (rename_term (upren xi) m)
  | App m n => App (rename_term xi m) (rename_term xi n)
  | Ind A s Cs => Ind (rename_term xi A) s (rename_terms (upren xi) Cs)
  | Constr i m => Constr i (rename_term xi m)
  | Case m Q Fs => 
    Case 
      (rename_term xi m)
      (rename_term xi Q)
      (rename_terms xi Fs)
  | DCase m Q Fs => 
    DCase 
      (rename_term xi m)
      (rename_term xi Q)
      (rename_terms xi Fs)
  | Fix m => Fix (rename_term (upren xi) m)
  end

with rename_terms (xi : var -> var) (ts : terms) : terms :=
  match ts with
  | Nil => Nil
  | Cons t ts => Cons (rename_term xi t) (rename_terms xi ts)
  end.

Instance Rename_term : Rename term. by apply: rename_term. Defined.

Fixpoint subst_term (sigma : var -> term) (t : term) : term :=
  match t with
  | Var x => sigma x
  | Sort s l => Sort s l
  | Prod A B s => Prod (subst_term sigma A) (subst_term (up sigma) B) s
  | Lolli A B s => Lolli (subst_term sigma A) (subst_term (up sigma) B) s
  | Lam m => Lam (subst_term (up sigma) m)
  | App m n => App (subst_term sigma m) (subst_term sigma n)
  | Ind A s Cs => Ind (subst_term sigma A) s (subst_terms (up sigma) Cs)
  | Constr i m => Constr i (subst_term sigma m)
  | Case m Q Fs => 
    Case 
      (subst_term sigma m)
      (subst_term sigma Q)
      (subst_terms sigma Fs)
  | DCase m Q Fs => 
    DCase 
      (subst_term sigma m)
      (subst_term sigma Q)
      (subst_terms sigma Fs)
  | Fix m => Fix (subst_term (up sigma) m)
  end

with subst_terms (sigma : var -> term) (ts : terms) : terms :=
  match ts with
  | Nil => Nil
  | Cons t ts => Cons (subst_term sigma t) (subst_terms sigma ts)
  end.

Instance Subst_term : Subst term. by apply: subst_term. Defined.

Lemma rename_subst xi m :
  rename_term xi m = subst_term (ren xi) m
with rename_subst' xi ls :
  rename_terms xi ls = subst_terms (ren xi) ls.
Proof.
  elim: m xi=> /={rename_subst} //.
    move=> A ih1 B ih2 s xi.
      rewrite ih1 ih2; by autosubst.
    move=> A ih1 B ih2 s xi.
      rewrite ih1 ih2; by autosubst.
    move=> m ih xi.
      rewrite ih; by autosubst.
    move=> m ih1 n ih2 xi.
      rewrite ih1 ih2; by autosubst.
    move=> A ih s Cs xi.
      rewrite ih rename_subst'; by autosubst.
    move=> i m ih xi.
      rewrite ih; by autosubst.
    move=> m ih1 Q ih2 Fs xi.
      rewrite ih1 ih2 rename_subst'; by autosubst.
    move=> m ih1 Q ih2 Fs xi.
      rewrite ih1 ih2 rename_subst'; by autosubst.
    move=> m ih xi.
      rewrite ih; by autosubst.
  elim: ls xi=> /={rename_subst'} //.
    move=> t t0 ih x1.
      rewrite ih rename_subst; by autosubst.
Qed.

Lemma subst_id m :
  subst_term ids m = m
with subst_id' ls :
  subst_terms ids ls = ls.
Proof.
  have up_id : up ids = ids.
    by apply: up_id_internal.
  elim: m=> /={subst_id} //; asimpl; try rewrite up_id.
    move=> A ih1 B ih2 s.
      rewrite ih1 ih2; by autosubst.
    move=> A ih1 B ih2 s.
      rewrite ih1 ih2; by autosubst.
    move=> m ih.
      rewrite ih; by autosubst.
    move=> m ih1 n ih2.
      rewrite ih1 ih2; by autosubst.
    move=> A ih s Cs.
      rewrite ih subst_id'; by autosubst.
    move=> i m ih.
      rewrite ih; by autosubst.
    move=> m ih1 Q ih2 Fs.
      rewrite ih1 ih2 subst_id'; by autosubst.
    move=> m ih1 Q ih2 Fs.
      rewrite ih1 ih2 subst_id'; by autosubst.
    move=> m ih.
      rewrite ih; by autosubst.
  elim: ls=> /={subst_id'} //.
    move=> t t0 ih.
      rewrite ih subst_id; by autosubst.
Qed.

Lemma ren_subst_comp xi sigma m :
  subst_term sigma (rename_term xi m) = subst_term (xi >>> sigma) m
with ren_subst_comp' xi sigma ls :
  subst_terms sigma (rename_terms xi ls) = subst_terms (xi >>> sigma) ls.
Proof.
  elim: m xi sigma=> /={ren_subst_comp} //; asimpl.
    move=> A ih1 B ih2 s xi sigma.
      rewrite ih1 ih2; by autosubst.
    move=> A ih1 B ih2 s xi sigma.
      rewrite ih1 ih2; by autosubst.
    move=> m ih xi sigma.
      rewrite ih; by autosubst.
    move=> m ih1 n ih2 xi sigma.
      rewrite ih1 ih2; by autosubst.
    move=> A ih s Cs xi sigma.
      rewrite ih ren_subst_comp'; by autosubst.
    move=> i m ih xi sigma.
      rewrite ih; by autosubst.
    move=> m ih1 Q ih2 Fs xi sigma.
      rewrite ih1 ih2 ren_subst_comp'; by autosubst.
    move=> m ih1 Q ih2 Fs xi sigma.
      rewrite ih1 ih2 ren_subst_comp'; by autosubst.
    move=> m ih xi sigma.
      rewrite ih; by autosubst.
  elim: ls xi sigma=> /={ren_subst_comp'} //; asimpl.
    move=> t t0 ih xi sigma.
      rewrite ih ren_subst_comp; by autosubst.
Qed.

Lemma subst_ren_comp sigma xi m :
  rename_term xi (subst_term sigma m) = subst_term (sigma >>> rename_term xi) m
with subst_ren_comp' sigma xi ls :
  rename_terms xi (subst_terms sigma ls) = subst_terms (sigma >>> rename_term xi) ls.
Proof.
  have up_comp_subst_ren : 
    forall sigma xi, 
      up (sigma >>> rename_term xi) = 
      up sigma >>> rename_term (upren xi).
    apply: up_comp_subst_ren_internal=> //.
      by apply: rename_subst. 
      by apply: ren_subst_comp.
  elim: m xi sigma=> /={subst_ren_comp} //; asimpl.
    move=> A ih1 B ih2 s xi sigma.
      rewrite ih1 ih2 up_comp_subst_ren; by autosubst.
    move=> A ih1 B ih2 s xi sigma.
      rewrite ih1 ih2 up_comp_subst_ren; by autosubst.
    move=> m ih xi sigma.
      rewrite ih up_comp_subst_ren; by autosubst.
    move=> m ih1 n ih2 xi sigma.
      rewrite ih1 ih2; by autosubst.
    move=> A ih s Cs xi sigma.
      rewrite ih up_comp_subst_ren subst_ren_comp'; by autosubst.
    move=> i m ih xi sigma.
      rewrite ih; by autosubst.
    move=> m ih1 Q ih2 Fs xi sigma.
      rewrite ih1 ih2 subst_ren_comp'; by autosubst.
    move=> m ih1 Q ih2 Fs xi sigma.
      rewrite ih1 ih2 subst_ren_comp'; by autosubst.
    move=> m ih xi sigma.
      rewrite ih up_comp_subst_ren; by autosubst.
  elim: ls xi sigma=> /={subst_ren_comp'} //; asimpl.
    move=> t t0 ih xi sigma.
      rewrite ih subst_ren_comp; by autosubst.
Qed.

Lemma subst_comp sigma tau m :
  subst_term tau (subst_term sigma m) = subst_term (sigma >> tau) m
with subst_comp' sigma tau ls :
  subst_terms tau (subst_terms sigma ls) = subst_terms (sigma >> tau) ls.
Proof.
  have up_comp : 
    forall sigma tau, up (sigma >> tau) = up sigma >> up tau.
    apply: up_comp_internal=> //.
      by apply: ren_subst_comp.
      by apply: subst_ren_comp.
  elim: m sigma tau=> /={subst_comp} //; asimpl.
    move=> A ih1 B ih2 s sigma tau.
      rewrite ih1 ih2 up_comp; by autosubst.
    move=> A ih1 B ih2 s sigma tau.
      rewrite ih1 ih2 up_comp; by autosubst.
    move=> m ih sigma tau.
      rewrite ih up_comp; by autosubst.
    move=> m ih1 n ih2 sigma tau.
      rewrite ih1 ih2; by autosubst.
    move=> A ih s Cs sigma tau.
      rewrite ih up_comp subst_comp'; by autosubst.
    move=> i m ih sigma tau.
      rewrite ih; by autosubst.
    move=> m ih1 Q ih2 Fs sigma tau.
      rewrite ih1 ih2 subst_comp'; by autosubst.
    move=> m ih1 Q ih2 Fs sigma tau.
      rewrite ih1 ih2 subst_comp'; by autosubst.
    move=> m ih sigma tau.
      rewrite ih up_comp; by autosubst.
  elim: ls sigma tau=> /={subst_comp'} //; asimpl.
    move=> t t0 ih sigma tau.
      rewrite ih subst_comp; by autosubst.
Qed.

Instance substLemmas_term : SubstLemmas term.
  constructor=> //.
  by apply: rename_subst.
  by apply: subst_id.
  by apply: subst_comp.
Qed.

Fixpoint spine (h : term) (ls : terms) : term :=
  match ls with
  | Nil => h
  | Cons m ls => spine (App h m) ls
  end.

Inductive iget : nat -> terms -> term -> Prop :=
| iget_O m ls :
  iget 0 (Cons m ls) m
| iget_S n m m' ls :
  iget n ls m ->
  iget (S n) (Cons m' ls) m.

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

with step' : terms -> terms -> Prop :=
| step'_Nil : step' Nil Nil
| step'_Cons1 m m' ls :
  step m m' ->
  step' (Cons m ls) (Cons m' ls)
| step'_Cons2 m ls ls' :
  step' ls ls' ->
  step' (Cons m ls) (Cons m ls').

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

with pstep' : terms -> terms -> Prop :=
| pstep'_Nil : pstep' Nil Nil
| pstep'_Cons m m' ls ls' :
  pstep m m' ->
  pstep' ls ls' ->
  pstep' (Cons m ls) (Cons m' ls').

Notation red := (star step).
Notation red' := (star step').
Notation conv := (conv step).
Notation conv' := (conv step').

Definition sred sigma tau := 
  forall x : var, red (sigma x) (tau x).

Lemma spine_subst sigma h ls :
  (spine h ls).[sigma] = spine (h.[sigma]) (ls..[sigma]).
Proof.
  move: sigma h. elim: ls => //.
  move=> a l ih sigma h.
    replace (a :: l)..[sigma] with (a.[sigma] :: l..[sigma])
      by autosubst; simpl.
    replace (App h.[sigma] a.[sigma]) with (App h a).[sigma]
      by autosubst.
    apply ih.
Qed.

Lemma iget_subst sigma i ls m :
  iget i ls m -> iget i ls..[sigma] m.[sigma].
Proof.
  move=> ig. elim: ig; asimpl.
  move=> m0 ls0.
    constructor.
  move=> n m0 m' ls0 ig ih.
    constructor=>//.
Qed.

Lemma step_subst sigma m n : 
  step m n -> step m.[sigma] n.[sigma]
with step'_subst sigma ls ls' : 
  step' ls ls' -> step' ls..[sigma] ls'..[sigma].
Proof.
  move=> st. elim: st sigma=> /={m n}; eauto using step.
    move=> m n sigma.
      replace (m.[n/].[sigma]) with (m.[up sigma].[n.[sigma]/])
        by autosubst.
      apply step_beta.
    move=> i m ms Q Fs F ig sigma.
      rewrite! spine_subst; asimpl.
      constructor.
      by apply: iget_subst.
    move=> i m ms Q Fs F ig sigma.
      rewrite! spine_subst; asimpl.
      constructor.
      by apply: iget_subst.
    move=> m sigma.
      replace m.[Fix m/].[sigma] with m.[up sigma].[Fix m.[up sigma]/]
        by autosubst.
      constructor.
  move=> st. elim: st sigma; asimpl; eauto using step'.
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

Lemma red_Ind' A s Cs1 Cs2 :
  red' Cs1 Cs2 -> red (Ind A s Cs1) (Ind A s Cs2).
Proof.
  move=> rd. elim: rd=> //.
  move=> y z rd' rd st.
  apply: star_trans.
  apply: rd.
  apply: star1; eauto using step.
Qed.

Lemma red_Ind A1 A2 s Cs1 Cs2 :
  red A1 A2 -> red' Cs1 Cs2 -> red (Ind A1 s Cs1) (Ind A2 s Cs2).
Proof.
  move=> A B. apply: (star_trans (Ind A2 s Cs1)).
  apply: (star_hom ((Ind^~ s)^~ Cs1)) A=> x y. exact: step_IndA.
  apply: red_Ind'=> //.
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

Lemma red'_h h h' ls :
  red h h' -> red' (h :: ls) (h' :: ls).
Proof.
  move=> rd. elim: rd ls=> //.
  move=> y z rd ih st ls.
    have st' : step' (y :: ls) (z :: ls).
      by apply: step'_cons1.
    apply: star_trans.
    apply: ih.
    by apply: star1.
Qed.

Lemma red'_ls h ls ls' :
  red' ls ls' -> red' (h :: ls) (h :: ls').
Proof.
  move=> rd. elim: rd h=> //.
  move=> y z rd ih st h.
    have st' : step' (h :: y) (h :: z).
      by apply: step'_cons2.
    apply: star_trans.
    apply: ih.
    by apply: star1.
Qed.

Lemma red'_subst sigma Cs Cs' :
  red' Cs Cs' -> red' Cs..[sigma] Cs'..[sigma].
Proof.
  move=> rd. elim: rd sigma=> /={Cs'}.
  move=> sigma //.
  move=> y z rd ih st sigma.
    have rd1 := ih sigma.
    apply: star_trans.
    apply rd1.
    move: st=> /(step'_subst sigma) rd2.
    by apply: star1.
Qed.

Lemma sred_up sigma tau : 
  sred sigma tau -> sred (up sigma) (up tau).
Proof. 
  move=> A [|n] //=; asimpl. 
  apply: red_subst. 
  exact: A. 
Qed.

Hint Resolve red_App red_Lam red_Prod red_Lolli red_Ind sred_up : red_congr.

Lemma red_compat sigma tau s : 
  sred sigma tau -> red s.[sigma] s.[tau].
Proof. 
  elim: s sigma tau=> *; asimpl; eauto 6 with red_congr.
  apply: red_Ind; eauto.

