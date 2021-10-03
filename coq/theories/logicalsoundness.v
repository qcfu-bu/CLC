From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program.
Require Import AutosubstSsr ARS Context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CoC.

Definition context T := seq (option T).
Definition cons_Some T (n : T) (Gamma : context T) : context T := 
  Some n :: Gamma.
Definition cons_None T (Gamma : context T) : context T := 
  None :: Gamma.

Notation "m :s Gamma" := (cons_Some m Gamma) (at level 30).
Notation ":n Gamma" := (cons_None Gamma) (at level 30).

Inductive has {T} `{Ids T} `{Subst T} : 
  context T -> var -> T -> Prop :=
| has_O m Gamma :
  has (m :s Gamma) 0 m.[ren (+1)]
| has_S Gamma v m n : 
  has Gamma v m ->
  has (n :s Gamma) (v.+1) m.[ren (+1)]
| has_N Gamma v m : 
  has Gamma v m ->
  has (:n Gamma) (v.+1) m.[ren (+1)].

Lemma has_x {T} `{Ids T} `{Subst T} (Gamma : context T) x A :
  has Gamma x A ->
  forall B,
    has Gamma x B ->
    A = B.
Proof.
  induction 1; intros.
  inv H1; eauto.
  inv H2; eauto.
  apply IHhas in H7. rewrite H7; eauto.
  inv H2; eauto.
  apply IHhas in H5. rewrite H5; eauto.
Qed.
  
Inductive term : Type :=
| Var (x : var)
| Sort (n : nat)
| App  (s t : term)
| Lam  (s : {bind term})
| Prod (s : term) (t : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
| value_sort l   : value (Sort l)
| value_var x    : value (Var x)
| value_prod A B : value (Prod A B)
| value_lam n    : value (Lam n).

Inductive step : term -> term -> Prop :=
| step_beta s t u :
  u = s.[t/] -> step (App (Lam s) t) u
| step_appL s1 s2 t :
  step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
  step t1 t2 -> step (App s t1) (App s t2)
| step_lam s1 s2 :
  step s1 s2 -> step (Lam s1) (Lam s2)
| step_prodL A1 A2 B :
  step A1 A2 -> step (Prod A1 B) (Prod A2 B)
| step_prodR A B1 B2 :
  step B1 B2 -> step (Prod A B1) (Prod A B2).

Inductive pstep : term -> term -> Prop :=
| pstep_beta s1 s2 t1 t2 u :
  u = s2.[t2/] ->
  pstep s1 s2 -> pstep t1 t2 -> pstep (App (Lam s1) t1) u
| pstep_var x : pstep (Var x) (Var x)
| pstep_sort n : pstep (Sort n) (Sort n)
| pstep_app s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep (App s1 t1) (App s2 t2)
| pstep_lam s1 s2 :
  pstep s1 s2 -> pstep (Lam s1) (Lam s2)
| pstep_prod s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep (Prod s1 t1) (Prod s2 t2).

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

Lemma pstep_refl s : pstep s s.
Proof.
  induction s; constructor; eauto.
Qed.

Axiom pstep_ren : forall s s' xi, 
  pstep s s' -> pstep s.[ren xi] s'.[ren xi].
Axiom church_rosser : CR pstep.

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".

Inductive has_type : context term -> term -> term -> Prop :=
| ty_var Gamma x A :
  has Gamma x A ->
  [ Gamma |- Var x :- A ]
| ty_sort Gamma n  :
  [ Gamma |- Sort n :- Sort n.+1 ]
| ty_prod Gamma A B n :
  [ Gamma |- A :- Sort n ] ->
  [ A :s Gamma |- B :- Sort n ] ->
  [ Gamma |- Prod A B :- Sort n ]
| ty_lam Gamma A B s n :
  [ Gamma |- Prod A B :- Sort n ] ->
  [ A :s Gamma |- s :- B ] ->
  [ Gamma |- Lam s :- Prod A B ]
| ty_app Gamma A B s t :
  [ Gamma |- s :- Prod A B ] ->
  [ Gamma |- t :- A ] ->
  [ Gamma |- App s t :- B.[t/] ]
| ty_conv Gamma A B s :
  A === B ->
  [ Gamma |- s :- A ] ->
  [ Gamma |- s :- B ]
where "[ Gamma |- s :- A ]" := (has_type Gamma s A).

Inductive context_ok : context term -> Prop :=
| ctx_nil :
  [ nil |- ]
| ctx_ncons Gamma A n :
  [ Gamma |- A :- Sort n ] ->
  [ Gamma |- ] ->
  [ A :s Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Notation "[ Gamma |- s ]" := (exists n, [ Gamma |- s :- Sort n ]).

Axiom weakening : 
  forall Gamma s A B,
  [ Gamma |- s :- A ] -> [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].

Axiom preservation :
  forall Gamma s A,
  [ Gamma |- ] -> 
  [ Gamma |- s :- A ] ->
  forall t, pstep s t -> [ Gamma |- t :- A ].

Axiom progress :
  forall s A,
  [ nil |- s :- A ] -> value s \/ exists s', step s s'.

Axiom strong_norm :
  forall Gamma s A,
  [ Gamma |- ] ->
  [ Gamma |- s :- A ] ->
  exists v, value v /\ s === v.

End CoC.

Require Import typesoundness.

Import DLTT.
Import CoC.

Fixpoint erase (m : DLTT.term) : CoC.term :=
  match m with
  | DLTT.Var x => CoC.Var x
  | DLTT.Sort _ l => CoC.Sort l
  | DLTT.TyProd A B _ => CoC.Prod (erase A) (erase B)
  | DLTT.LnProd A B _ => CoC.Prod (erase A) (erase B)
  | DLTT.Arrow A B _ => CoC.Prod (erase A) (erase B).[ren (+1)]
  | DLTT.Lolli A B _ => CoC.Prod (erase A) (erase B).[ren (+1)]
  | DLTT.Lam n => CoC.Lam (erase n)
  | DLTT.App m n => CoC.App (erase m) (erase n)
  end.

Fixpoint erase_context 
  (Gamma : DLTT.context DLTT.term) 
: CoC.context CoC.term :=
  match Gamma with
  | Left t :: Gamma => erase t :s erase_context Gamma
  | Right t :: Gamma => erase t :s erase_context Gamma
  | Null :: Gamma => :n erase_context Gamma
  | nil => nil
  end.

Notation "[| m |]" := (erase m).
Notation "[[ Gamma ]]" := (erase_context Gamma).

Definition erase_subst 
  (sigma : var -> DLTT.term) 
  (tau : var -> CoC.term)
: Prop := 
  forall x, [|sigma x|] = tau x.

Lemma erase_ren_com m :
  forall xi, [| m |].[ren xi] = [| m.[ren xi] |].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm IHm0; eauto.
  - rewrite IHm1. 
    replace ([|m2|].[ren (xi >>> (+1))])
      with ([|m2|].[ren xi].[ren (+1)]) by autosubst.
    rewrite IHm2; eauto.
  - rewrite IHm1. 
    replace ([|m2|].[ren (xi >>> (+1))])
      with ([|m2|].[ren xi].[ren (+1)]) by autosubst.
    rewrite IHm2; eauto.
  - rewrite IHm; eauto.
  - rewrite IHm1 IHm2; eauto.
Qed.

Lemma erase_subst_up sigma tau :
  erase_subst sigma tau -> erase_subst (up sigma) (up tau).
Proof.
  unfold erase_subst.
  intros.
  induction x; asimpl; eauto.
  rewrite <-H.
  rewrite erase_ren_com; eauto.
Qed.

Lemma erase_subst_com m :
  forall sigma tau, 
    erase_subst sigma tau ->
    [| m.[sigma] |] = [| m |].[tau].
Proof.
  induction m; intros; asimpl; eauto.
  - rewrite <- (IHm sigma); eauto.
    rewrite <- (IHm0 (up sigma)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm sigma); eauto.
    rewrite <- (IHm0 (up sigma)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm1 sigma); eauto.
    rewrite (IHm2 _ tau); autosubst.
  - rewrite <- (IHm1 sigma); eauto.
    rewrite (IHm2 _ tau); autosubst.
  - rewrite <- (IHm (up sigma)); eauto.
    apply erase_subst_up; eauto.
  - rewrite <- (IHm1 sigma); eauto.
    rewrite <- (IHm2 sigma); eauto.
Qed.

Lemma erase_pstep m n :
  DLTT.pstep m n -> CoC.pstep [|m|] [|n|].
Proof with eauto using pstep, pstep_refl.
  induction 1; simpl; intros...
  eapply pstep_beta; eauto.
  apply erase_subst_com.
  unfold erase_subst; intros.
  destruct x; asimpl; eauto.
  constructor; eauto.
  apply pstep_ren; eauto.
  constructor; eauto.
  apply pstep_ren; eauto.
Qed.

Lemma erase_conv m n :
  conv DLTT.pstep m n -> conv CoC.pstep [|m|] [|n|].
Proof.
  induction 1; eauto.
  eapply conv_trans.
  apply IHconv.
  eapply convSE; eauto.
  apply erase_pstep; eauto.
  eapply convSEi; eauto.
  apply erase_pstep; eauto.
Qed.

Lemma hasL_erase Gamma x A :
  hasL Gamma x A -> has [[ Gamma ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Lemma hasR_erase Gamma x A :
  hasR Gamma x A -> has [[ Gamma ]] x [| A |].
Proof.
  intros.
  dependent induction H; asimpl; firstorder.
  rewrite <- erase_ren_com; constructor.
  rewrite <- erase_ren_com; constructor; eauto.
  rewrite <- erase_ren_com; constructor; eauto.
Qed.

Inductive agree_wk : 
  CoC.context CoC.term -> CoC.context CoC.term -> Prop :=
| agree_wk_nil : agree_wk nil nil
| agree_wk_s Gamma1 Gamma2 e :
  agree_wk Gamma1 Gamma2 ->
  agree_wk (e :: Gamma1) (e :: Gamma2)
| agree_wk_n Gamma1 Gamma2 A :
  agree_wk Gamma1 Gamma2 ->
  agree_wk (:n Gamma1) (A :s Gamma2).

Lemma agree_wk_has Gamma1 Gamma2 :
  agree_wk Gamma1 Gamma2 ->
  forall x A,
    has Gamma1 x A ->
    has Gamma2 x A.
Proof.
  intro H.
  dependent induction H; simpl; intros; eauto.
  inv H0; constructor; eauto.
  inv H0; constructor; eauto.
Qed.

Lemma agree_wk_re Gamma :
  agree_wk [[re Gamma]] [[Gamma]].
Proof.
  induction Gamma.
  - simpl; constructor.
  - destruct a; simpl; constructor; eauto.
Qed.

Lemma agree_wk_merge_inv Gamma1 Gamma2 Gamma :
  merge Gamma1 Gamma2 Gamma ->
  agree_wk [[Gamma1]] [[Gamma]] /\
  agree_wk [[Gamma2]] [[Gamma]].
Proof with eauto using agree_wk.
  intro H.
  dependent induction H; simpl; firstorder...
Qed.

Lemma wk_ok Gamma1 m A : 
  [ Gamma1 |- m :- A ] ->
  forall Gamma2, agree_wk Gamma1 Gamma2 ->
    [ Gamma2 |- m :- A ].
Proof.
  intro H.
  dependent induction H; simpl; intros; subst.
  - pose proof (agree_wk_has H0 H).
    apply ty_var; eauto.
  - apply ty_sort.
  - apply ty_prod.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_lam.
    apply IHhas_type1; eauto.
    apply IHhas_type2; constructor; eauto.
  - eapply ty_app.
    apply IHhas_type1; eauto.
    apply IHhas_type2; eauto.
  - eapply ty_conv.
    apply H.
    apply IHhas_type; eauto.
Qed.

Lemma erase_re Gamma m A :
  [ [[re Gamma]] |- m :- A ] ->
  [ [[Gamma]] |- m :- A ].
Proof.
  intro H.
  eapply wk_ok; eauto.
  apply agree_wk_re.
Qed.

Lemma erase_ok Gamma m A s : 
  [ Gamma |- m :- A -: s ] ->
  [ [[ Gamma ]] |- [| m |] :- [| A |] ].
Proof.
  intro H.
  dependent induction H; asimpl.
  - apply ty_sort.  
  - apply ty_prod.
    apply IHhas_type1.
    apply IHhas_type2.
  - apply ty_prod.
    apply IHhas_type1.
    apply IHhas_type2.
  - apply ty_prod.
    apply IHhas_type1.
    replace (Sort l) with ((Sort l).[ren (+1)]) by autosubst.
    apply weakening.
    apply IHhas_type2.
  - apply ty_prod.
    apply IHhas_type1.
    replace (Sort l) with ((Sort l).[ren (+1)]) by autosubst.
    apply weakening.
    apply IHhas_type2.
  - apply hasL_erase in H.
    apply ty_var; eauto.
  - apply hasR_erase in H.
    apply ty_var; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
    rewrite erase_ren_com; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
    apply erase_re; eauto.
  - simpl in IHhas_type1.
    simpl in IHhas_type2.
    eapply ty_lam; eauto.
    apply erase_re; eauto.
    rewrite erase_ren_com; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[[|n|]/] === App (Lam [|B|]) [|n|]).
    eapply convSEi; eauto.
    econstructor; eauto using pstep_refl.
    eapply ty_conv.
    apply H2.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[ren (+1)].[[|n|]/] = [|B|]) by autosubst.
    eapply ty_conv.
    rewrite <- H2; eauto.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[[|n|]/] === App (Lam [|B|]) [|n|]).
    eapply convSEi; eauto.
    econstructor; eauto using pstep_refl.
    eapply ty_conv.
    apply H2.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - simpl in IHhas_type1.
    assert ([|B|].[ren (+1)].[[|n|]/] = [|B|]) by autosubst.
    eapply ty_conv.
    rewrite <- H2; eauto.
    apply agree_wk_merge_inv in H1; destruct H1.
    eapply ty_app; eauto.
    eapply wk_ok; eauto.
    eapply wk_ok; eauto.
  - eapply ty_conv.
    apply erase_conv; eauto.
    apply IHhas_type.
Qed.