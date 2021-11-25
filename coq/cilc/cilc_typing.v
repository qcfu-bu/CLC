From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Reserved Notation "[ Γ |- ]".
Reserved Notation "[ Γ |- m :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| u_Sort Γ s l : 
  pure Γ ->
  [ Γ |- s @ l :- U @ l.+1 ]
| u_Prod Γ A B s l :
  pure Γ ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- B :- s @ l ] ->
  [ Γ |- Prod A B U :- U @ l ]
| l_Prod Γ A B s l :
  pure Γ ->
  [ Γ |- A :- L @ l ] ->
  [ +n Γ |- B :- s @ l ] ->
  [ Γ |- Prod A B L :- U @ l ]
| u_Lolli Γ A B s l :
  pure Γ ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- B :- s @ l ] ->
  [ Γ |- Lolli A B U :- L @ l ]
| l_Lolli Γ A B s l :
  pure Γ ->
  [ Γ |- A :- L @ l ] ->
  [ +n Γ |- B :- s @ l ] ->
  [ Γ |- Lolli A B L :- L @ l ]
| u_Var Γ x A : 
  hasU Γ x A ->
  [ Γ |- Var x :- A ]
| l_Var Γ x A :
  hasL Γ x A ->
  [ Γ |- Var x :- A ]
| u_Lam Γ n A B s t l :
  pure Γ ->
  [ Γ |- Prod A B s :- t @ l ] ->
  [ A +{s} Γ |- n :- B ] ->
  [ Γ |- Lam A n s :- Prod A B s ]
| l_Lam Γ n A B s t l :
  [ re Γ |- Lolli A B s :- t @ l ] ->
  [ A +{s} Γ |- n :- B ] ->
  [ Γ |- Lam A n s :- Lolli A B s ]
| u_Prod_App Γ1 Γ2 Γ A B m n :
  pure Γ2 ->
  [ Γ1 |- m :- Prod A B U ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| l_Prod_App Γ1 Γ2 Γ  A B m n :
  [ Γ1 |- m :- Prod A B L ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| u_Lolli_App Γ1 Γ2 Γ A B m n :
  pure Γ2 ->
  [ Γ1 |- m :- Lolli A B U ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| l_Lolli_App Γ1 Γ2 Γ A B m n :
  [ Γ1 |- m :- Lolli A B L ] ->
  [ Γ2 |- n :- A ] ->
  merge Γ1 Γ2 Γ ->
  [ Γ |- App m n :- B.[n/] ]
| s_Ind Γ A Cs s t l :
  arity s A ->
  List.Forall (constr 0 s) Cs ->
  pure Γ ->
  [ Γ |- A :- U @ l ] ->
  List.Forall (fun C => [ A +u Γ |- C :- t @ l ]) Cs ->
  [ Γ |- Ind A Cs s :- A ]
| s_Constr Γ A s i C Cs :
  let I := Ind A Cs s in
  iget i Cs C ->
  pure Γ ->
  [ Γ |- I :- A ] ->
  [ Γ |- Constr i I :- C.[I/] ]
| s_Case Γ1 Γ2 Γ A Q s s' Fs Cs m ms :
  let I := Ind A Cs s in
  arity s A ->
  merge Γ1 Γ2 Γ ->
  [ Γ1 |- m :- spine I ms ] ->
  [ re Γ2 |- Q :- arity1 s' A ] ->
  All2 (fun F C =>
    constr 0 s C /\
    [ Γ2 |- F :- case I Q C ]) Fs Cs ->
  [ Γ |- Case m Q Fs :- spine Q ms ]
| s_DCase Γ1 Γ2 Γ A Q s Fs Cs m ms :
  let I := Ind A Cs U in
  arity U A ->
  pure Γ1 ->
  merge Γ1 Γ2 Γ ->
  [ Γ1 |- m :- spine I ms ] ->
  [ re Γ2 |- Q :- arity2 s I A ] ->
  All2i (fun i F C =>
    constr 0 U C /\
    [ Γ2 |- F :- dcase I Q (Constr i I) C ]) 0 Fs Cs ->
  [ Γ |- DCase m Q Fs :- App (spine Q ms) m ]
| u_Fix Γ A m l :
  pure Γ ->
  [ Γ |- A :- U @ l ] ->
  [ A +u Γ |- m :- A.[ren (+1)] ] ->
  [ Γ |- Fix A m :- A ]
| s_Conv Γ A B m s l :
  A <: B ->
  [ re Γ |- B :- s @ l ] ->
  [ Γ |- m :- A ] ->
  [ Γ |- m :- B ]
where "[ Γ |- m :- A ]" := (has_type Γ m A).

Section has_type_nested_ind.
  Variable P : context term -> term -> term -> Prop.
  Hypothesis ih_u_Sort : forall Γ s l, 
    pure Γ -> P Γ (s @ l) (U @ l.+1).
  Hypothesis ih_u_Prod : forall Γ A B s l,
    pure Γ ->
    [ Γ |- A :- U @ l ] -> P Γ A (U @ l) ->
    [ A +u Γ |- B :- s @ l ] -> P (A +u Γ) B (s @ l) ->
    P Γ (Prod A B U) (U @ l).
  Hypothesis ih_l_Prod : forall Γ A B s l,
    pure Γ ->
    [ Γ |- A :- L @ l] -> P Γ A (L @ l) ->
    [ +n Γ |- B :- s @ l ] -> P (+n Γ) B (s @ l) ->
    P Γ (Prod A B L) (U @ l).
  Hypothesis ih_u_Lolli : forall Γ A B s l,
    pure Γ ->
    [ Γ |- A :- U @ l ] -> P Γ A (U @ l) ->
    [ A +u Γ |- B :- s @ l ] -> P (A +u Γ) B (s @ l) ->
    P Γ (Lolli A B U) (L @ l). 
  Hypothesis ih_l_Lolli : forall Γ A B s l,
    pure Γ ->
    [ Γ |- A :- L @ l ] -> P Γ A (L @ l) ->
    [ +n Γ |- B :- s @ l ] -> P (+n Γ) B (s @ l) ->
    P Γ (Lolli A B L) (L @ l).
  Hypothesis ih_u_Var : forall Γ x A,
    hasU Γ x A -> P Γ (Var x) A.
  Hypothesis ih_l_Var : forall Γ x A,
    hasL Γ x A -> P Γ (Var x) A.
  Hypothesis ih_u_Lam : forall Γ n A B s t l,
    pure Γ ->
    [ Γ |- Prod A B s :- Sort t l ] -> 
      P Γ (Prod A B s) (Sort t l) ->
    [ A +{s} Γ |- n :- B ] -> 
      P (A +{s} Γ) n B ->
    P Γ (Lam A n s) (Prod A B s).
  Hypothesis ih_l_Lam : forall Γ n A B s t l,
    [ re Γ |- Lolli A B s :- Sort t l ] -> 
      P (re Γ) (Lolli A B s) (Sort t l) ->
    [ A +{s} Γ |- n :- B ] ->
      P (A +{s} Γ) n B ->
    P Γ (Lam A n s) (Lolli A B s).
  Hypothesis ih_u_Prod_App : forall Γ1 Γ2 Γ A B m n,
    pure Γ2 ->
    [ Γ1 |- m :- Prod A B U ] -> P Γ1 m (Prod A B U) ->
    [ Γ2 |- n :- A ] -> P Γ2 n A ->
    merge Γ1 Γ2 Γ ->
    P Γ (App m n) B.[n/].
  Hypothesis ih_l_Prod_App : forall Γ1 Γ2 Γ A B m n,
    [ Γ1 |- m :- Prod A B L ] -> P Γ1 m (Prod A B L) ->
    [ Γ2 |- n :- A ] -> P Γ2 n A ->
    merge Γ1 Γ2 Γ ->
    P Γ (App m n) B.[n/].
  Hypothesis ih_u_Lolli_App : forall Γ1 Γ2 Γ A B m n,
    pure Γ2 ->
    [ Γ1 |- m :- Lolli A B U ] -> P Γ1 m (Lolli A B U) ->
    [ Γ2 |- n :- A ] -> P Γ2 n A ->
    merge Γ1 Γ2 Γ ->
    P Γ (App m n) B.[n/].
  Hypothesis ih_l_Lolli_App : forall Γ1 Γ2 Γ A B m n,
    [ Γ1 |- m :- Lolli A B L ] -> P Γ1 m (Lolli A B L) ->
    [ Γ2 |- n :- A ] -> P Γ2 n A ->
    merge Γ1 Γ2 Γ ->
    P Γ (App m n) B.[n/].
  Hypothesis ih_s_Ind : forall Γ A Cs s t l,
    arity s A ->
    List.Forall (constr 0 s) Cs ->
    pure Γ ->
    [ Γ |- A :- Sort U l ] -> P Γ A (Sort U l) ->
    List.Forall (fun C => [ A +u Γ |- C :- Sort t l ]) Cs ->
      List.Forall (fun C => P (A +u Γ) C (Sort t l)) Cs ->
    P Γ (Ind A Cs s) A.
  Hypothesis ih_s_Constr : forall Γ A s i C Cs,
    let I := Ind A Cs s in
    iget i Cs C ->
    pure Γ ->
    [ Γ |- I :- A ] -> P Γ I A ->
    P Γ (Constr i I) C.[I/].
  Hypothesis ih_s_Case : forall Γ1 Γ2 Γ A Q s s' Fs Cs m ms,
    let I := Ind A Cs s in
    arity s A ->
    merge Γ1 Γ2 Γ ->
    [ Γ1 |- m :- spine I ms ] -> P Γ1 m (spine I ms) ->
    [ re Γ2 |- Q :- arity1 s' A ] -> P (re Γ2) Q (arity1 s' A) ->
    All2 (fun F C =>
      constr 0 s C /\
      [ Γ2 |- F :- case I Q C ]) Fs Cs ->
    All2 (fun F C =>
      constr 0 s C /\
      P Γ2 F (case I Q C)) Fs Cs ->
    P Γ (Case m Q Fs) (spine Q ms).
  Hypothesis ih_s_DCase : forall Γ1 Γ2 Γ A Q s Fs Cs m ms,
    let I := Ind A Cs U in
    arity U A ->
    pure Γ1 ->
    merge Γ1 Γ2 Γ ->
    [ Γ1 |- m :- spine I ms ] -> P Γ1 m (spine I ms) ->
    [ re Γ2 |- Q :- arity2 s I A ] -> P (re Γ2) Q (arity2 s I A) ->
    All2i (fun i F C =>
      constr 0 U C /\
      [ Γ2 |- F :- (dcase I Q (Constr i I) C) ]) 0 Fs Cs ->
    All2i (fun i F C =>
      constr 0 U C /\
      P Γ2 F (dcase I Q (Constr i I) C)) 0 Fs Cs ->
    P Γ (DCase m Q Fs) (App (spine Q ms) m).
  Hypothesis ih_u_Fix : forall Γ A m l,
    pure Γ ->
    [ Γ |- A :- Sort U l ] -> P Γ A (Sort U l) ->
    [ A +u Γ |- m :- A.[ren (+1)] ] -> P (A +u Γ) m A.[ren (+1)] ->
    P Γ (Fix A m) A.
  Hypothesis ih_s_Conv : forall Γ A B m s l,
    A <: B ->
    [ re Γ |- B :- Sort s l ] -> P (re Γ) B (Sort s l) ->
    [ Γ |- m :- A ] -> P Γ m A ->
    P Γ m B.

  Fixpoint has_type_nested_ind 
    Γ m A (pf : [ Γ |- m :- A ]) : P Γ m A.
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
            (fun C => [ A0 +u Γ0 |- C :- Sort t l]) Cs) :
          List.Forall (fun C => P (A0 +u Γ0) C (Sort t l)) Cs
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
            [ Γ2 |- F :- case I Q C ]) Fs Cs) :
          All2 (fun F C => 
            constr 0 s C /\
            P Γ2 F (case I Q C)) Fs Cs
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
            [ Γ2 |- F :- dcase I Q (Constr i I) C ]) n Fs Cs) :
          All2i (fun i F C => 
            constr 0 U C /\
            P Γ2 F (dcase I Q (Constr i I) C)) n Fs Cs
        :=
          match pf in 
            All2i _ n Fs Cs
          return
            All2i (fun i F C => 
              constr 0 U C /\
              P Γ2 F (dcase I Q (Constr i I) C)) n Fs Cs
          with
          | All2i_nil _ => All2i_nil _ _
          | All2i_cons _ _ _ _ _ (conj h1 h2) pfTl =>
            All2i_cons (conj h1 (has_type_nested_ind _ _ _ h2)) (fold _ _ _ pfTl)
          end); eauto.
    eapply ih_u_Fix; eauto.
    eapply ih_s_Conv; eauto.
  Qed.
End has_type_nested_ind.

Lemma u_Prod_max Γ A B s l1 l2 :
  pure Γ ->
  [ Γ |- A :- U @ l1 ] ->
  [ A +u Γ |- B :- s @ l2 ] ->
  [ Γ |- Prod A B U :- U @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Γ |- A :- U @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ A +u Γ |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: u_Prod; eauto.
Qed.

Lemma l_Prod_max Γ A B s l1 l2 :
  pure Γ ->
  [ Γ |- A :- L @ l1 ] ->
  [ +n Γ |- B :- s @ l2 ] ->
  [ Γ |- Prod A B L :- U @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Γ |- A :- L @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ +n Γ |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: l_Prod; eauto.
Qed.

Lemma u_Lolli_max Γ A B s l1 l2 :
  pure Γ ->
  [ Γ |- A :- U @ l1 ] ->
  [ A +u Γ |- B :- s @ l2 ] ->
  [ Γ |- Lolli A B U :- L @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Γ |- A :- U @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ A +u Γ |- B :- s @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt2.
    constructor. apply: re_pure.
    apply: tyB.
  apply: u_Lolli; eauto.
Qed.

Lemma l_Lolli_max Γ A B s l1 l2 :
  pure Γ ->
  [ Γ |- A :- L @ l1 ] ->
  [ +n Γ |- B :- s @ l2 ] ->
  [ Γ |- Lolli A B L :- L @ (maxn l1 l2) ].
Proof.
  move=>p tyA tyB.
  have lt1 : l1 <= maxn l1 l2.
    by apply: leq_maxl.
  have lt2 : l2 <= maxn l1 l2.
    by apply: leq_maxr.
  have tyA' : [ Γ |- A :- L @ (maxn l1 l2) ].
    apply: s_Conv.
    apply: sub_Sort.
    apply: lt1.
    constructor. apply: re_pure.
    apply: tyA.
  have tyB' : [ +n Γ |- B :- s @ (maxn l1 l2) ].
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
| u_ok Γ A l :
  [ Γ |- ] ->
  [ re Γ |- A :- Sort U l ] ->
  [ A +u Γ |- ]
| l_ok Γ A l :
  [ Γ |- ] ->
  [ re Γ |- A :- Sort L l ] ->
  [ A +l Γ |- ]
| n_ok Γ :
  [ Γ |- ] ->
  [ +n Γ |- ]
where "[ Γ |- ]" := (context_ok Γ).

Lemma re_ok Γ :
  [ Γ |- ] ->
  [ re Γ |- ].
Proof with eauto using context_ok.
  elim...
  move{Γ}=> Γ A l wf1 wf2 ty //=.
  apply: u_ok...
  rewrite <-re_re...
Qed.