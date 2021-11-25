From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS cilc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
| step_Fiξota A m :
  step (Fix A m) (m.[Fix A m/]).

Notation red := (star step).
Notation "m === n" := (conv step m n) (at level 50).

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
  Hypothesis ih_Fiξota :
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
    apply ih_Fiξota; eauto.
  Qed.
End step_ind_nested.