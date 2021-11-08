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

Ltac fold_subst :=
  fold subst_term;
  fold Subst_term;
  fold subst.

Definition sing t := Cons t Nil.

Fixpoint append (ls1 ls2 : terms) : terms :=
  match ls1 with
  | Nil => ls2
  | Cons h ls1 => Cons h (append ls1 ls2)
  end.

Fixpoint rev (ls : terms) : terms :=
  match ls with
  | Nil => Nil
  | Cons t ls => append (rev ls) (sing t)
  end.

Fixpoint spine (h : term) (ls : terms) : term :=
  match ls with
  | Nil => h
  | Cons m ls => spine (App h m) ls
  end.

Fixpoint spine' (h : term) (ls : terms) : term :=
  match ls with
  | Nil => h
  | Cons m ls => App (spine' h ls) m
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
  iget i Fs F ->
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
  iget i Fs F ->
  iget i Fs' F' ->
  pstep' ms ms' ->
  pstep' Fs Fs' ->
  pstep F F' ->
  pstep 
    (DCase (spine (Constr i m) ms) Q Fs)
    (spine F' ms')
| pstep_Fix m m' :
  pstep m m' ->
  pstep (Fix m) (Fix m')
| pstep_FixIota m m' :
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
Notation conv' := (conv step').
Notation conv := (conv step).

Definition sred sigma tau := 
  forall x : var, red (sigma x) (tau x).

Lemma append_Nil ls : append ls Nil = ls.
Proof. elim: ls=>//=. by move=> t ls ->. Qed.

Lemma append_Cons m ls1 ls2 :
  append (Cons m ls1) ls2 = Cons m (append ls1 ls2).
Proof. by elim: ls1. Qed.

Lemma append_assoc (xs ys zs : terms) :
  append xs (append ys zs) = append (append xs ys) zs.
Proof. elim: xs=> //=. by move=> t t0 ->. Qed.

Lemma rev_append_distr (xs ys : terms) :
  rev (append xs ys) = append (rev ys) (rev xs).
Proof.
  elim: xs ys=> //=.
  move=> ys. by rewrite append_Nil.
  move=> t ls ih ys. by rewrite ih append_assoc.
Qed.

Lemma rev_sing h ls :
  rev (append ls (sing h)) = Cons h (rev ls).
Proof. exact: rev_append_distr. Qed.

Lemma rev_rev ls : rev (rev ls) = ls.
Proof.
  elim: ls=> //=.
  move=> t ls e. by rewrite rev_sing e.
Qed.

Lemma append_sing_False h ls : ~Nil = append ls (sing h).
Proof. elim: ls h=> //=. Qed.

Lemma append_inj ls1 ls2 t1 t2 :
  append ls1 (sing t1) = append ls2 (sing t2) ->
    ls1 = ls2 /\ t1 = t2.
Proof.
  elim: ls1 ls2 t1 t2=> //=.
  move=> ls1 t1 t2.
    destruct ls1=> //= e.
    by inv e.
    rewrite /sing in e.
    inv e.
    by move: H1=> /append_sing_False.
  move=> t ls1 ih ls2 t1 t2.
    destruct ls2=> //= e.
    rewrite /sing in e.
    inv e.
    exfalso.
    apply: append_sing_False.
    by rewrite <- H1.
    inv e.
    by move: H1=> /ih[->->].
Qed.

Lemma rev_inj ls1 ls2 : rev ls1 = rev ls2 -> ls1 = ls2.
Proof.
  elim: ls1 ls2=> //=.
  move=> ls2. by destruct ls2=> //= /append_sing_False.
  move=> t ls1 ih ls2.
    destruct ls2=> //= e.
    exfalso.
    apply: append_sing_False.
    by rewrite <- e.
    move: e=> /append_inj[e1->].
    by move: e1=> /ih ->.
Qed.

Lemma spine_append h xs ys :
  spine h (append xs ys) = spine (spine h xs) ys.
Proof. elim: xs ys h=> //=. Qed.

Lemma spine_rev h m ls :
  App (spine h (rev ls)) m = spine h (rev (Cons m ls)).
Proof.
  elim: ls h m=> //=.
  move=> t ls ih h m.
  rewrite spine_append=> //=.
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
  by rewrite rev_rev in pf.
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
  (spine h ls).[sigma] = spine (h.[sigma]) (subst_terms sigma ls).
Proof.
  move: sigma h. elim: ls => //.
  move=> a l ih sigma h.
    replace (subst_terms sigma (Cons a l)) 
      with (Cons a.[sigma] (subst_terms sigma l))
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
  iget i ls m -> iget i (subst_terms sigma ls) m.[sigma].
Proof.
  move=> ig. elim: ig; asimpl.
  move=> m0 ls0; by constructor.
  move=> n m0 m' ls0 ig ih; by constructor.
Qed.

Lemma step_subst sigma m n : 
  step m n -> step m.[sigma] n.[sigma]
with step'_subst sigma ls ls' : 
  step' ls ls' -> step' (subst_terms sigma ls) (subst_terms sigma ls').
Proof.
  move=> st. elim: st sigma=> /={m n}; eauto using step.
    move=> m n sigma.
      replace (m.[n/].[sigma]) with (m.[up sigma].[n.[sigma]/])
        by autosubst.
      apply step_Beta.
    move=> i m ms Q Fs F ig sigma; fold_subst.
      rewrite! spine_subst; asimpl.
      constructor.
      by apply: iget_subst.
    move=> i m ms Q Fs F ig sigma; fold_subst.
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

Lemma red_Ind A1 A2 s Cs1 Cs2 :
  red A1 A2 -> red' Cs1 Cs2 -> red (Ind A1 s Cs1) (Ind A2 s Cs2).
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
  red m1 m2 -> red Q1 Q2 -> red' Fs1 Fs2 -> red (Case m1 Q1 Fs1) (Case m2 Q2 Fs2).
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
  red m1 m2 -> red Q1 Q2 -> red' Fs1 Fs2 -> red (DCase m1 Q1 Fs1) (DCase m2 Q2 Fs2).
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

Lemma red'_h h1 h2 ls :
  red h1 h2 -> red' (Cons h1 ls) (Cons h2 ls).
Proof.
  move=> rd. elim: rd ls=> //.
  move=> y z rd ih st ls.
  apply: star_trans.
    by apply: ih.
    by apply: star1; constructor.
Qed.

Lemma red'_ls h ls ls' :
  red' ls ls' -> red' (Cons h ls) (Cons h ls').
Proof.
  move=> rd. elim: rd h=> //.
  move=> y z rd ih st h.
  apply: star_trans.
    by apply: ih.
    by apply: star1; constructor.
Qed.

Lemma red'_Nil ls : red' Nil ls -> ls = Nil.
Proof. 
  elim=> //.
  move=> y z _ -> st. by inv st.
Qed.

Lemma red'_Cons m ls l : 
  red' (Cons m ls) l -> 
    exists m' ls', l = Cons m' ls' /\ red m m' /\ red' ls ls'.
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
  red h h' -> red' ls ls' -> red (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=> ls' h h' rd /red'_Nil -> //.
  move=> t t0 ih ls' h h' rd rd'=> //=.
  apply: (star_trans (spine (App h' t) t0)).  
    apply: ih=> //.
    exact: red_App.
  move: rd'=> /red'_Cons [m [ls [-> [rd1 rd2]]]] //=.
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
  red_subst sred_up 
: red_congr.

Lemma red_compat sigma tau s : 
  sred sigma tau -> red s.[sigma] s.[tau]
with red_compat' sigma tau ls :
  sred sigma tau -> red' (subst_terms sigma ls) (subst_terms tau ls).
Proof. 
  elim: s sigma tau=> /={red_compat}; asimpl; eauto 6 with red_congr.
  elim: ls sigma tau=> /={red_compat'}; asimpl; eauto 6 with red_congr.
    move=> t t0 ih sigma tau sr.
    apply: star_trans.
      apply: red'_h; exact: red_compat.
      apply: red'_ls; exact: ih.
Qed.

Definition sconv (sigma tau : var -> term) := 
  forall x, conv (sigma x) (tau x).

Lemma conv_Lam m1 m2 : conv m1 m2 -> conv (Lam m1) (Lam m2).
Proof. apply: conv_hom=> x y. exact: step_Lam. Qed.

Lemma conv_Prod A1 A2 s B1 B2 :
  conv A1 A2 -> conv B1 B2 -> conv (Prod A1 B1 s) (Prod A2 B2 s).
Proof.
  move=> A B.
  apply: (conv_trans (Prod A2 B1 s)).
  apply: (conv_hom ((Prod^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Prod A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_Lolli A1 A2 s B1 B2 :
  conv A1 A2 -> conv B1 B2 -> conv (Lolli A1 B1 s) (Lolli A2 B2 s).
Proof.
  move=> A B.
  apply: (conv_trans (Lolli A2 B1 s)).
  apply: (conv_hom ((Lolli^~ B1)^~ s)) A => x y ps.
    by constructor.
  apply: (conv_hom ((Lolli A2)^~ s)) B => x y ps.
    by constructor.
Qed.

Lemma conv_App m1 m2 n1 n2 :
  conv m1 m2 -> conv n1 n2 -> conv (App m1 n1) (App m2 n2).
Proof.
  move=> A B.
  apply: (conv_trans (App m2 n1)).
  apply: (conv_hom (App^~ n1)) A=> x y ps.
    by constructor.
  apply: conv_hom B=> x y ps.
    by constructor.
Qed.

Lemma conv_Ind A1 A2 s Cs1 Cs2 :
  conv A1 A2 -> conv' Cs1 Cs2 -> conv (Ind A1 s Cs1) (Ind A2 s Cs2).
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
  conv m1 m2 -> conv (Constr i m1) (Constr i m2).
Proof.
  move=> A.
  apply: (conv_hom (Constr i)) A => x y. exact: step_Constr.
Qed.

Lemma conv_Case m1 m2 Q1 Q2 Fs1 Fs2 :
  conv m1 m2 -> conv Q1 Q2 -> conv' Fs1 Fs2 -> conv (Case m1 Q1 Fs1) (Case m2 Q2 Fs2).
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
  conv m1 m2 -> conv Q1 Q2 -> conv' Fs1 Fs2 -> conv (DCase m1 Q1 Fs1) (DCase m2 Q2 Fs2).
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
  conv m1 m2 -> conv (Fix m1) (Fix m2).
Proof.
  move=> A.
  apply: (conv_hom Fix) A=> x y. exact: step_Fix.
Qed.

Lemma conv'_h h1 h2 ls :
  conv h1 h2 -> conv' (Cons h1 ls) (Cons h2 ls).
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

Lemma conv'_ls h ls ls' :
  conv' ls ls' -> conv' (Cons h ls) (Cons h ls').
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

Lemma conv_subst sigma m n :
  conv m n -> conv m.[sigma] n.[sigma].
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
  conv_subst sconv_up 
: conv_congr.

Lemma conv_compat sigma tau s : 
  sconv sigma tau -> conv s.[sigma] s.[tau]
with conv_compat' sigma tau ls :
  sconv sigma tau -> conv' (subst_terms sigma ls) (subst_terms tau ls).
Proof. 
  elim: s sigma tau=> {conv_compat}; asimpl; eauto 6 with conv_congr.
  elim: ls sigma tau=> {conv_compat'}; asimpl; eauto 6 with conv_congr.
    move=> t t0 ih sigma tau sr.
    apply: conv_trans.
      apply: conv'_h; exact: conv_compat.
      apply: conv'_ls; exact: ih.
Qed.

Lemma conv_Beta s t1 t2 : conv t1 t2 -> conv s.[t1/] s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s
with pstep_refl' ls : pstep' ls ls.
Proof. 
  elim: s=> /={pstep_refl}; eauto using pstep.
  elim: ls=> /={pstep_refl'}; eauto using pstep'.
Qed.

Lemma step_pstep m m' : step m m' -> pstep m m'
with step_pstep' ls ls' : step' ls ls' -> pstep' ls ls'.
Proof with eauto using pstep, pstep', pstep_refl, pstep_refl'.
  elim {step_pstep}...
  elim {step_pstep'}...
Qed.

Lemma pstep_red m m' : pstep m m' -> red m m'
with pstep_red' ls ls' : pstep' ls ls' -> red' ls ls'.
Proof.
  elim=> {m m' pstep_red} //=; eauto with red_congr.
    move=> m m' n n' p1 r1 p2 r2.
      apply: starES.
      by econstructor.
      apply: (star_trans (m'.[n.:Var])). exact: red_subst.
      by apply: red_compat => -[|].
    move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 r.
      have ih1 := pstep_red' _ _ p1=> {p1}.
      have ih2 := pstep_red' _ _ p2=> {p2}.
      apply: star_trans.
      apply: red_Case.
      apply: red_spine.
      exact: starR.
      exact: ih1.
      exact: starR.
      exact: ih2.
      apply: star1.
      by constructor.
    move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 r.
      have ih1 := pstep_red' _ _ p1=> {p1}.
      have ih2 := pstep_red' _ _ p2=> {p2}.
      apply: star_trans.
      apply: red_DCase.
      apply: red_spine.
      exact: starR.
      exact: ih1.
      exact: starR.
      exact: ih2.
      apply: star1.
      by constructor.
    move=> m m' p r.
      apply: star_trans.
      apply: red_Fix.
      exact: r.
      apply: star1.
      by constructor.
  elim=> {ls ls' pstep_red'} //=.
    move=> m m' ls ls' p1 p2 r.
    apply: (star_trans (Cons m' ls)).
      apply: red'_h. exact: pstep_red.
      exact: red'_ls.
Qed.

Lemma pstep_subst sigma m m' :
  pstep m m' -> pstep m.[sigma] m'.[sigma]
with pstep_subst' sigma ls ls' :
  pstep' ls ls' -> pstep' (subst_terms sigma ls) (subst_terms sigma ls').
Proof with eauto using pstep, pstep', pstep_refl, pstep_refl'.
  move=> p. elim: p sigma => {m m' pstep_subst}...
  move=> m m' n n' p1 ih1 p2 ih2 sigma; asimpl.
    have h1 := (ih1 (up sigma))=> {ih1}.
    have h2 := (ih2 sigma)=> {ih2}.
    have h3 := pstep_Beta (h1 Ids_term Rename_term) h2.
    by asimpl in h3.
  move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 ih sigma=> //=; fold_subst.
    rewrite! spine_subst; fold_subst.
    apply: pstep_CaseIota; eauto.
    apply: iget_subst. exact ig.
    apply: iget_subst. exact ig'.
  move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 ih sigma=> //=; fold_subst.
    rewrite! spine_subst; fold_subst.
    apply: pstep_DCaseIota; eauto.
    apply: iget_subst. exact ig.
    apply: iget_subst. exact ig'.
  move=> m m' p ih sigma; asimpl.
    replace m'.[Fix m'.[up sigma] .: sigma]
      with (m'.[up sigma]).[Fix m'.[up sigma]/]
      by autosubst.
    exact: pstep_FixIota.
  elim=> {ls ls' pstep_subst'}...
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
  pstep m m' -> psstep sigma tau -> pstep m.[sigma] m'.[tau]
with pstep_compat' sigma tau ls ls' :
  pstep' ls ls' -> 
    psstep sigma tau -> pstep' (subst_terms sigma ls) (subst_terms tau ls').
Proof with eauto 6 using pstep, pstep', psstep_up.
  move=> p. 
  elim: p sigma tau => {m m' pstep_compat}...
    move=> m m' n n' p1 ih1 p2 ih2 sigma tau ps1; asimpl.
      have ps2 := psstep_up ps1.
      have h1 := ih1 _ _ ps2.
      have h2 := ih2 _ _ ps1.
      have h3 := pstep_Beta h1 h2.
      by asimpl in h3.
    move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 ih sigma tau ps=> //=; fold_subst.
      rewrite! spine_subst; fold_subst.
      apply: pstep_CaseIota.
      apply: iget_subst. exact: ig.
      apply: iget_subst. exact: ig'.
      exact: pstep_compat'.
      exact: pstep_compat'.
      exact: ih.
    move=> i m ms ms' Q Fs Fs' F F' ig ig' p1 p2 p3 ih sigma tau ps=> //=; fold_subst.
      rewrite! spine_subst; fold_subst.
      apply: pstep_DCaseIota.
      apply: iget_subst. exact: ig.
      apply: iget_subst. exact: ig'.
      exact: pstep_compat'.
      exact: pstep_compat'.
      exact: ih.
    move=> m m' p ih sigma tau ps; asimpl.
      replace m'.[Fix m'.[up tau] .: tau]
        with (m'.[up tau]).[Fix m'.[up tau]/]
        by autosubst.
      constructor.
      apply: ih.
      exact: psstep_up.
  elim=> {ls ls' pstep_compat'}...
Qed.

Lemma psstep_compat sigma tau m1 m2 :
  psstep sigma tau -> pstep m1 m2 -> psstep (m1 .: sigma) (m2 .: tau).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep, pstep', pstep_refl, pstep_refl'.
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

Lemma pstep'_iget1 ls ls' i m :
  pstep' ls ls' -> iget i ls m -> exists m', iget i ls' m' /\ pstep m m'.
Proof with eauto using iget.
  move=> p.
  elim: p m i => {ls ls'}.
  move=> m i ig. inv ig.
  move=> m m' ls ls' p1 p2 ih m0 i ig. inv ig.
    exists m'...
    move: H3=> /ih [m'0 [ig p]].
    exists m'0...
Qed.

Lemma pstep'_iget2 ls ls' i m' :
  pstep' ls ls' -> iget i ls' m' -> exists m, iget i ls m /\ pstep m m'.
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
  pstep h h' -> pstep' ls ls' -> pstep (spine h ls) (spine h' ls').
Proof.
  elim: ls ls' h h'.
  move=> ls' h h' p1 p2. inv p2=> //=.
  move=> t t0 ih ls h h' p p'. inv p'=> //=.
  apply: ih=> //.
  exact: pstep_App.
Qed.

Lemma pstep_spine_inv h ls m :
  pstep (spine h ls) m -> (~ exists m, h = Lam m) -> 
    exists h' ls', m = spine h' ls' /\ pstep h h' /\ pstep' ls ls'.
Proof with eauto using pstep, pstep', pstep_refl, pstep_refl'.
  elim: ls h m.
  move=> h m //= p nx.
  exists m; exists Nil...
  move=> t t0 ih h m //= p nx.
  move: p=> /ih p.
  have pf : ~ (exists m, App h t = Lam m).
    apply: all_not_not_ex=> n.
    have pf := classic (App h t = Lam n).
    inv pf=> //.
  move: pf=> /p [h' [ls' [-> [p1 p2]]]].
  inv p1.
  exists m'; exists (Cons n' ls')...
  exfalso.
  apply: nx.
  by exists m0.
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 -> exists m', pstep m1 m' /\ pstep m2 m'
with pstep_diamond' ls ls1 ls2 :
  pstep' ls ls1 -> pstep' ls ls2 -> exists ls', pstep' ls1 ls' /\ pstep' ls2 ls'.
Proof with eauto 6 using pstep, pstep', pstep_compat_Beta, pstep_spine.
  move=> p. 
  elim: p m2=> {m m1 pstep_diamond}.
    move=> x m2 p. inv p. exists (Var x)...
    move=> srt l m2 p. inv p. exists (Sort srt l)...
    move=> n n' p1 ih m2 p2. inv p2.
      move: H0=> /ih [m' [p2 p3]].
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
    move=> A A' s Cs Cs' p1 ih p2 m2 p3. inv p3.
      move: H3=> /ih [m' [p3 p4]].
      move: (pstep_diamond' _ _ _ p2 H4)=> [ls' [p5 p6]].
      exists (Ind m' s ls')...
    move=> i m m' p1 ih m2 p2. inv p2.
      move: H2=> /ih [m'1 [p2 p3]].
      exists (Constr i m'1)...
    move=> m m' Q Q' Fs Fs' p1 ih1 p2 ih2 p3 m2 p4. inv p4.
      move: H2=> /ih1 [m'1 [p4 p5]].
      move: H4=> /ih2 [m'2 [p6 p7]].
      move: (pstep_diamond' _ _ _ p3 H5)=> [ls' [p8 p9]].
      exists (Case m'1 m'2 ls')...
      have pf :  ~(exists m : term, Constr i m0 = Lam m).
        move=> [m e] //=.
      move: p1=> /pstep_spine_inv p1.
      move: pf=> /p1 [h' [ls'0 [-> [p4 p6]]]]. inv p4. 
      move: (pstep_diamond' _ _ _ p6 H4)=> [ls' [p7 p8]].
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
    move=> m m' Q Q' Fs Fs' p1 ih1 p2 ih2 p3 m2 p4. inv p4.
      move: H2=> /ih1 [m'1 [p4 p5]].
      move: H4=> /ih2 [m'2 [p6 p7]].
      move: (pstep_diamond' _ _ _ p3 H5)=> [ls' [p8 p9]].
      exists (DCase m'1 m'2 ls')...
      have pf :  ~(exists m : term, Constr i m0 = Lam m).
        move=> [m e] //=.
      move: p1=> /pstep_spine_inv p1.
      move: pf=> /p1 [h' [ls'0 [-> [p4 p6]]]]. inv p4. 
      move: (pstep_diamond' _ _ _ p6 H4)=> [ls' [p7 p8]].
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
      
