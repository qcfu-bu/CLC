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
| s_DCase Gamma1 Gamma2 Gamma A Q s Fs Cs m ms :
  let I := Ind A Cs U in
  arity U A ->
  pure Gamma1 ->
  merge Gamma1 Gamma2 Gamma ->
  [ Gamma1 |- m :- spine I ms ] ->
  [ re Gamma2 |- Q :- arity2 s I A ] ->
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
  Hypothesis ih_s_DCase : forall Gamma1 Gamma2 Gamma A Q s Fs Cs m ms,
    let I := Ind A Cs U in
    arity U A ->
    pure Gamma1 ->
    merge Gamma1 Gamma2 Gamma ->
    [ Gamma1 |- m :- spine I ms ] -> P Gamma1 m (spine I ms) ->
    [ re Gamma2 |- Q :- arity2 s I A ] -> P (re Gamma2) Q (arity2 s I A) ->
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