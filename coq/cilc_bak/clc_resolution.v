From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine clc_respine clc_iota_lemma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value : term -> Prop :=
| value_sort s l :
  value (s @ l)
| value_pi A B s r t :
  value (Pi A B s r t)
| value_lam A m s t :
  value (Lam A m s t)
| value_indd A Cs s ms :
  value (spine (Ind A Cs s) ms)
| value_constr i I s ms :
  All1 value ms ->
  value (spine (Constr i I s) ms)
| value_fix A m :
  value (Fix A m)
| value_ptr l :
  value (Ptr l).

Section value_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_sort : forall s l, P (s @ l).
  Hypothesis ih_pi : forall A B s r t, P (Pi A B s r t).
  Hypothesis ih_lam : forall A m s t, P (Lam A m s t).
  Hypothesis ih_indd :
    forall A Cs s ms, P (spine (Ind A Cs s) ms).
  Hypothesis ih_constr :
    forall i I s ms,
      All1 value ms -> All1 P ms ->
      P (spine (Constr i I s) ms).
  Hypothesis ih_fix : forall A m, P (Fix A m).
  Hypothesis ih_ptr : forall l, P (Ptr l).

  Fixpoint value_ind_nested m (pf : value m) : P m.
  Proof.
    case pf; intros.
    apply: ih_sort; eauto.
    apply: ih_pi; eauto.
    apply: ih_lam; eauto.
    apply: ih_indd; eauto.
    have ih_nested:=
      fix fold ms (pf : All1 value ms) : All1 P ms :=
        match pf with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (value_ind_nested _ hd) (fold _ tl)
        end; eauto.
    apply: ih_fix; eauto.
    apply: ih_ptr; eauto.
  Qed.
End value_ind_nested.

Inductive pad (Θ : context term) : context term -> Prop :=
| pad_O : pad Θ Θ
| pad_U Θ' m : pad Θ Θ' -> pad Θ (m :U Θ')
| pad_N Θ' : pad Θ Θ' -> pad Θ (_: Θ').

Inductive free : context term -> nat -> term -> context term -> Prop :=
| free_U Θ m l :
  l = length Θ ->
  free (Some (m, U) :: Θ) l m (Some (m, U) :: Θ)
| free_L Θ m l :
  l = length Θ ->
  free (Some (m, L) :: Θ) l m (None :: Θ)
| free_S Θ Θ' m n l :
  free Θ l m Θ' ->
  free (n :: Θ) l m (n :: Θ').

Inductive resolve : context term -> term -> term -> Prop :=
| resolve_var Θ x :
  Θ |> U ->
  resolve Θ (Var x) (Var x)
| resolve_sort Θ s l :
  Θ |> U ->
  resolve Θ (Sort s l) (Sort s l)
| resolve_pi Θ A A' B B' s r t :
  Θ |> U ->
  resolve Θ A A' ->
  resolve Θ B B' ->
  resolve Θ (Pi A B s r t) (Pi A' B' s r t)
| resolve_lam Θ A A' m m' s t :
  Θ |> t ->
  resolve [Θ] A A' ->
  resolve Θ m m' ->
  resolve Θ (Lam A m s t) (Lam A' m' s t)
| resolve_app Θ1 Θ2 Θ m m' n n' :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve Θ2 n n' ->
  resolve Θ (App m n) (App m' n')
| resolve_indd Θ A A' Cs Cs' s :
  Θ |> U ->
  resolve Θ A A' ->
  All2 (resolve Θ) Cs Cs' ->
  resolve Θ (Ind A Cs s) (Ind A' Cs' s)
| resolve_constr Θ i I I' s :
  Θ |> U ->
  resolve Θ I I' ->
  resolve Θ (Constr i I s) (Constr i I' s)
| resolve_case Θ1 Θ2 Θ m m' Q Q' Fs Fs' :
  Θ1 ∘ Θ2 => Θ ->
  resolve Θ1 m m' ->
  resolve [Θ2] Q Q' ->
  All2 (resolve Θ2) Fs Fs' ->
  resolve Θ (Case m Q Fs) (Case m' Q' Fs')
| resolve_fix Θ A A' m m' :
  Θ |> U ->
  resolve Θ A A' ->
  resolve Θ m m' ->
  resolve Θ (Fix A m) (Fix A' m')
| resolve_ptr Θ Θ' l m m' :
  free Θ l m Θ' ->
  resolve Θ' m m' ->
  resolve Θ (Ptr l) m'.

Section resolve_ind_nested.
  Variable P : context term -> term -> term -> Prop.
  Hypothesis ih_var :
    forall Θ x, Θ |> U -> P Θ (Var x) (Var x).
  Hypothesis ih_sort :
    forall Θ s l, Θ |> U -> P Θ (Sort s l) (Sort s l).
  Hypothesis ih_pi :
    forall Θ A A' B B' s r t,
      Θ |> U ->
      resolve Θ A A' -> P Θ A A' ->
      resolve Θ B B' -> P Θ B B' ->
      P Θ (Pi A B s r t) (Pi A' B' s r t).
  Hypothesis ih_lam :
    forall Θ A A' m m' s t,
      Θ |> t ->
      resolve [Θ] A A' -> P [Θ] A A' ->
      resolve Θ m m' -> P Θ m m' ->
      P Θ (Lam A m s t) (Lam A' m' s t).
  Hypothesis ih_app :
    forall Θ1 Θ2 Θ m m' n n',
      Θ1 ∘ Θ2 => Θ ->
      resolve Θ1 m m' -> P Θ1 m m' ->
      resolve Θ2 n n' -> P Θ2 n n' ->
      P Θ (App m n) (App m' n').
  Hypothesis ih_indd :
    forall Θ A A' Cs Cs' s,
      Θ |> U ->
      resolve Θ A A' -> P Θ A A' ->
      All2 (resolve Θ) Cs Cs' -> All2 (P Θ) Cs Cs' ->
      P Θ (Ind A Cs s) (Ind A' Cs' s).
  Hypothesis ih_constr :
    forall Θ i I I' s,
      Θ |> U ->
      resolve Θ I I' -> P Θ I I' ->
      P Θ (Constr i I s) (Constr i I' s).
  Hypothesis ih_case :
    forall Θ1 Θ2 Θ m m' Q Q' Fs Fs',
      Θ1 ∘ Θ2 => Θ ->
      resolve Θ1 m m' -> P Θ1 m m' ->
      resolve [Θ2] Q Q' -> P [Θ2] Q Q' ->
      All2 (resolve Θ2) Fs Fs' -> All2 (P Θ2) Fs Fs' ->
      P Θ (Case m Q Fs) (Case m' Q' Fs').
  Hypothesis ih_fix :
    forall Θ A A' m m',
      Θ |> U ->
      resolve Θ A A' -> P Θ A A' ->
      resolve Θ m m' -> P Θ m m' ->
      P Θ (Fix A m) (Fix A' m').
  Hypothesis ih_ptr :
    forall Θ Θ' l m m',
      free Θ l m Θ' ->
      resolve Θ' m m' -> P Θ' m m' ->
      P Θ (Ptr l) m'.

  Fixpoint resolve_ind_nested
    Θ m m' (pf : resolve Θ m m') : P Θ m m'.
  Proof.
    case pf; intros.
    apply: ih_var; eauto.
    apply: ih_sort; eauto.
    apply: ih_pi; eauto.
    apply: ih_lam; eauto.
    apply: ih_app; eauto.
    have ih_nested :=
      fix fold Cs Cs' (pf : All2 (resolve Θ0) Cs Cs') :
        All2 (P Θ0) Cs Cs' :=
        match pf with
        | All2_nil => All2_nil _
        | All2_cons _ _ _ _ hd tl =>
          All2_cons (resolve_ind_nested _ _ _ hd) (fold _ _ tl)
        end; eauto.
    apply: ih_constr; eauto.
    have ih_nested :=
      fix fold Fs Fs' (pf : All2 (resolve Θ2) Fs Fs') :
        All2 (P Θ2) Fs Fs' :=
        match pf with
        | All2_nil => All2_nil _
        | All2_cons _ _ _ _ hd tl =>
          All2_cons (resolve_ind_nested _ _ _ hd) (fold _ _ tl)
        end; eauto.
    apply: ih_fix; eauto.
    apply: ih_ptr; eauto.
  Qed.
End resolve_ind_nested.

Inductive resolved : term -> Prop :=
| resolved_var x :
  resolved (Var x)
| resolved_sort s l :
  resolved (Sort s l)
| resolved_pi A B s r t :
  resolved A ->
  resolved B ->
  resolved (Pi A B s r t)
| resolved_lam A m s t :
  resolved A ->
  resolved m ->
  resolved (Lam A m s t)
| resolved_app m n :
  resolved m ->
  resolved n ->
  resolved (App m n)
| resolved_indd A Cs s :
  resolved A ->
  All1 resolved Cs ->
  resolved (Ind A Cs s)
| resolved_constr i I s :
  resolved I ->
  resolved (Constr i I s)
| resolved_case m Q Fs :
  resolved m ->
  resolved Q ->
  All1 resolved Fs ->
  resolved (Case m Q Fs)
| resolved_fix A m :
  resolved A ->
  resolved m ->
  resolved (Fix A m).

Section resolved_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_var : forall x, P (Var x).
  Hypothesis ih_sort : forall s l, P (Sort s l).
  Hypothesis ih_pi :
    forall A B s r t,
      resolved A -> P A ->
      resolved B -> P B ->
      P (Pi A B s r t).
  Hypothesis ih_lam :
    forall A m s t,
      resolved A -> P A ->
      resolved m -> P m ->
      P (Lam A m s t).
  Hypothesis ih_app :
    forall m n,
      resolved m -> P m ->
      resolved n -> P n ->
      P (App m n).
  Hypothesis ih_indd :
    forall A Cs s,
      resolved A -> P A ->
      All1 resolved Cs -> All1 P Cs ->
      P (Ind A Cs s).
  Hypothesis ih_constr :
    forall i I s,
      resolved I -> P I ->
      P (Constr i I s).
  Hypothesis ih_case :
    forall m Q Fs,
      resolved m -> P m ->
      resolved Q -> P Q ->
      All1 resolved Fs -> All1 P Fs ->
      P (Case m Q Fs).
  Hypothesis ih_fix :
    forall A m,
      resolved A -> P A ->
      resolved m -> P m ->
      P (Fix A m).

  Fixpoint resolved_ind_nested
    m (pf : resolved m) : P m.
  Proof.
    case pf; intros.
    apply: ih_var; eauto.
    apply: ih_sort; eauto.
    apply: ih_pi; eauto.
    apply: ih_lam; eauto.
    apply: ih_app; eauto.
    have ih_nested:=
      fix fold Cs (pf : All1 resolved Cs) : All1 P Cs :=
        match pf with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (resolved_ind_nested _ hd) (fold _ tl)
        end; eauto.
    apply: ih_constr; eauto.
    have ih_nested:=
      fix fold Fs (pf : All1 resolved Fs) : All1 P Fs :=
        match pf with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (resolved_ind_nested _ hd) (fold _ tl)
        end; eauto.
    apply: ih_fix; eauto.
  Qed.
End resolved_ind_nested.

Lemma pad_re Θ Θp : pad Θ Θp -> pad [Θ] [Θp].
Proof with eauto using pad. elim... Qed.

Lemma pad_pure Θ Θ' : pad [Θ] Θ' -> Θ' |> U.
Proof with eauto using key. elim... apply: re_pure. Qed.

Lemma pad_mergeL Θ1 Θ2 Θ Θ1p :
  pad Θ1 Θ1p -> Θ1 ∘ Θ2 => Θ ->
  exists Θ2p Θp,
    pad Θ2 Θ2p /\ pad Θ Θp /\ Θ1p ∘ Θ2p => Θp.
Proof with eauto 6 using pad, merge.
  move=>pd. elim: pd Θ2 Θ=>{Θ1p}.
  move=>Θ2 Θ mrg.
  exists Θ2. exists Θ...
  move=>Θ' m pd ih Θ2 Θ /ih[Θ2p[Θp[pd1[pd2 mrg]]]].
  exists (m :U Θ2p). exists (m :U Θp)...
  move=>Θ' pd ih Θ2 Θ /ih[Θ2p[Θp[pd1[pd2 mrg]]]].
  exists (_: Θ2p). exists (_: Θp)...
Qed.

Lemma pad_mergeR Θ1 Θ2 Θ Θ2p :
  pad Θ2 Θ2p -> Θ1 ∘ Θ2 => Θ ->
  exists Θ1p Θp,
    pad Θ1 Θ1p /\ pad Θ Θp /\ Θ1p ∘ Θ2p => Θp.
Proof.
  move=>pd /merge_sym mrg.
  have[Θ1p[Θp[pd1[pd2 /merge_sym mrgx]]]]:=pad_mergeL pd mrg.
  exists Θ1p. exists Θp; eauto.
Qed.

Lemma pad_merge Θ1 Θ2 Θ Θp :
  pad Θ Θp -> Θ1 ∘ Θ2 => Θ ->
  exists Θ1p Θ2p,
    pad Θ1 Θ1p /\ pad Θ2 Θ2p /\ Θ1p ∘ Θ2p => Θp.
Proof with eauto 6 using pad, merge.
  move=>pd. elim: pd Θ1 Θ2=>{Θp}.
  move=>Θ1 Θ2 mrg.
  exists Θ1. exists Θ2...
  move=>Θ' m pd ih Θ1 Θ2 /ih[Θ1p[Θ2p[pd1[pd2 mrg]]]].
  exists (m :U Θ1p). exists (m :U Θ2p)...
  move=>Θ' pd ih Θ1 Θ2 /ih[Θ1p[Θ2p[pd1[pd2 mrg]]]].
  exists (_: Θ1p). exists (_: Θ2p)...
Qed.

Lemma resolve_resolved Θ m m' : resolve Θ m m' -> resolved m'.
Proof with eauto using resolved, All1.
  move: Θ m m'. apply: resolve_ind_nested...
  move=>Θ A A' Cs Cs' s k rA ihA rCs ihCs.
  { constructor...
    elim: ihCs rCs=>{Cs Cs'}...
    move=>C C' Cs Cs' rC' hd ih tl.
    inv tl.
    constructor... }
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg rm ihm rQ ihQ rFs ihFs.
  { constructor...
    elim: ihFs rFs=>{Fs Fs'}...
    move=>F F' Fs Fs' rF' hd ih tl.
    inv tl.
    constructor... }
Qed.

Inductive well_resolved :
  context term -> term -> term -> term -> sort -> Prop :=
| Well_resolved Θ m n A t :
  resolve Θ m n -> nil ⊢ n : A : t -> well_resolved Θ m n A t.

Lemma resolve_wkU Θ A A' m :
  resolve Θ A A' -> resolve (m :U Θ) A A'.
Proof with eauto using resolve, key, merge, All2.
  move=>rA. move: Θ A A' rA m.
  apply: resolve_ind_nested...
  move=>Θ A A' m m' s [|]...
  move=>Θ A A' Cs Cs' s k rA ihA rCs ihCs m.
  { apply: resolve_indd...
    elim: ihCs rCs=>{Cs Cs'}...
    move=>C C' Cs Cs' h hd ih tl.
    inv tl.
    constructor... }
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg rm ihm rQ ihQ rFs ihFs n.
  { apply: resolve_case...
    elim: ihFs rFs=>{Fs Fs'}...
    move=>F F' Fs Fs' h hd ih tl.
    inv tl.
    constructor... }
  move=>Θ Θ' l m m' fr rm ihm n.
  have{}ihm:=ihm n.
  econstructor...
  econstructor...
Qed.

Lemma resolve_wkN Θ A A' :
  resolve Θ A A' -> resolve (_: Θ) A A'.
Proof with eauto using resolve, key, merge, All2.
  move=>rA. move: Θ A A' rA.
  apply: resolve_ind_nested...
  move=>Θ Θ' l m m' fr rs ih.
  econstructor...
  econstructor...
Qed.

Lemma resolve_pad Θ Θ' A A' :
  pad Θ Θ' -> resolve Θ A A' -> resolve Θ' A A'.
Proof with eauto using resolve_wkU, resolve_wkN.
  move=>pd. elim: pd A A'=>{Θ'}...
Qed.

Lemma resolve_type_refl_All2i Θ A Q Fs Cs k s s' i :
  let I := Ind A Cs s in
  All2i
    (fun i F C =>
       constr 0 s C /\
         forall (T := mkcase k s' I Q (Constr i I s) C) Θ, resolve [Θ] F F) i Fs Cs ->
  All2 (resolve [Θ]) Fs Fs.
Proof with eauto using All2.
  move=>//=ihFs.
  elim: ihFs=>{i Fs Cs}...
  move=>i F C Fs Cs [_ ih] hd tl.
  constructor...
Qed.

Lemma resolve_type_refl Θ Γ m A s : Γ ⊢ m : A : s -> resolve [Θ] m m.
Proof with eauto using resolve, re_pure, merge_re_id, All2.
  move=>ty. move: Γ m A s ty Θ.
  apply: clc_type_ind_nested...
  move=>Γ A B m s r t i k tyP rsP tym rsm Θ.
  { apply: resolve_lam...
    apply: re_sort.
    have{}rsP:=rsP Θ.
    inv rsP. rewrite<-re_invo... }
  move=>Γ A Cs s l k ar _ tyA ihA tyCs ihCs Θ.
  { apply: resolve_indd...
    elim: ihCs tyCs=>{Cs}...
    move=>C Cs h hd ih tl.
    inv tl.
    constructor... }
  move=>Γ1 Γ2 Γ A Q s s' k Fs Cs m ms I leq ar key mrg
    tym ihm tyQ ihQ tyFs ihFs Θ.
  { apply: resolve_case...
    apply: resolve_type_refl_All2i... }
  Unshelve. all: eauto.
Qed.

Lemma resolve_type_id_All2i Θ A Q Cs Fs Fs' k s s' i :
  let I := Ind A Cs s in
  All2i
    (fun i F C =>
       constr 0 s C /\
         forall (T := mkcase k s' I Q (Constr i I s) C) Θ n, resolve Θ F n -> F = n) i Fs Cs ->
  All2 (resolve Θ) Fs Fs' ->
  Fs = Fs'.
Proof.
  move=>//=ihFs h.
  elim: h i Cs ihFs=>//={Fs Fs'}.
  move=>F F' Fs Fs' rF rFs ih i Cs tl. inv tl.
  move: H2=>[_ h].
  f_equal; eauto.
Qed.

Lemma resolve_type_id Θ Γ m n A s :
  Γ ⊢ m : A : s -> resolve Θ m n -> m = n.
Proof with eauto using resolve, re_pure, merge_re_id, re_pure, All1.
  move=>ty. move: Γ m A s ty Θ n.
  apply: clc_type_ind_nested=>//.
  move=>Γ s l k Θ n rs. inv rs...
  move=>Γ A B s r t i k tyA ihA tyB ihB Θ n rs. inv rs.
  { erewrite ihA...
    erewrite ihB... }
  move=>Γ x A s hs Θ n rs. inv rs...
  move=>Γ A B m s r t i k tyP ihP tym ihm Θ n rs. inv rs.
  { have[l[tyA[_[_ tyB]]]]:=pi_inv tyP.
    have/ihP[->]:resolve [Θ] (Pi A B s r t) (Pi A' B s r t).
    { constructor...
      apply: resolve_type_refl... }
    erewrite ihm... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn Θ n0 rs. inv rs.
  { erewrite ihm...
    erewrite ihn... }
  move=>Γ A Cs s l k ar _ tyA ihA tyCs ihCs Θ n rs. inv rs.
  { f_equal...
    elim: H6 ihCs tyCs=>{Cs Cs'}...
    move=>C C' Cs Cs' rs hCs hd ih tl. inv ih. inv tl.
    f_equal... }
  move=>Γ A s i C Cs I k ig tyI ihI Θ n rs. inv rs.
  { erewrite ihI... }
  move=>Γ1 Γ2 Γ A Q s s' k Fs Cs m ms I leq ar key mrg
    tym ihm tyQ ihQ tyFs ihFs Θ n rs. inv rs.
  { f_equal...
    apply: resolve_type_id_All2i... }
  move=>Γ A m l k tyA ihA tym ihm Θ n rs. inv rs.
  { erewrite ihA...
    erewrite ihm... }
  Unshelve. all: eauto.
Qed.

Lemma free_length Θ l n Θ' : free Θ l n Θ' -> l < length Θ.
Proof.
  elim=>{Θ l n Θ'}.
  move=>Θ m l->//=.
  move=>Θ m l->//=.
  move=>Θ Θ' m n l fr leq//=.
  apply: leq_trans.
  exact: leq.
  eauto.
Qed.

Lemma free_inv Θ Θ' m n t :
  free (m :{t} Θ) (length Θ) n Θ' ->
  m = n /\
  match t with
  | U => m :{t} Θ
  | L => _: Θ
  end = Θ'.
Proof.
  elim: Θ Θ' m n=>//=.
  move=>Θ' m n fr. inv fr=>//. inv H4.
  move=>m Θ ih Θ' m0 n fr=>//. inv fr=>//.
  exfalso.
  inv H4.
  have:(length Θ).+1 - (length Θ) = (length Θ) - (length Θ).
  by rewrite H5.
  rewrite subnn.
  rewrite subSnn=>//.
  have:(length Θ).+1 - (length Θ) = (length Θ) - (length Θ).
  by rewrite H5.
  rewrite subnn.
  rewrite subSnn=>//.
  move/free_length in H5.
  have le :length Θ < (length Θ).+2 by eauto.
  have h:= leq_trans H5 le.
  unfold leq in h.
  rewrite subSnn in h.
  move/eqnP in h; inv h.
Qed.

Lemma free_empty Θ Θ' n : ~free (_: Θ) (length Θ) n Θ'.
Proof.
  elim: Θ Θ' n=>//=.
  move=>Θ' n fr. inv fr. inv H4.
  move=>m Θ ih Θ' n fr=>//. inv fr=>//.
  exfalso.
  inv H4.
  have:(length Θ).+1 - (length Θ) = (length Θ) - (length Θ).
  by rewrite H5.
  rewrite subnn.
  rewrite subSnn=>//.
  have:(length Θ).+1 - (length Θ) = (length Θ) - (length Θ).
  by rewrite H5.
  rewrite subnn.
  rewrite subSnn=>//.
  move/free_length in H5.
  have le :length Θ < (length Θ).+2 by eauto.
  have h:= leq_trans H5 le.
  unfold leq in h.
  rewrite subSnn in h.
  move/eqnP in h; inv h.
Qed.

Lemma free_merge Θ1 Θ2 Θ3 Θ l m :
  free Θ1 l m Θ3 -> Θ1 ∘ Θ2 => Θ ->
    exists Θ4, free Θ l m Θ4 /\ Θ3 ∘ Θ2 => Θ4.
Proof with eauto using free, merge.
  move=>fr. elim: fr Θ2 Θ=>{Θ1 Θ3 l m}.
  move=>Θ m l e Θ2 Θ0 mrg. inv mrg.
  exists (m :U Γ). split...
  econstructor.
  have[->_]//=:=merge_length H3.
  move=>Θ m l e Θ2 Θ0 mrg. inv mrg.
  exists (_: Γ). split...
  econstructor.
  have[->_]//:=merge_length H3.
  move=>Θ Θ' m n l fr ih Θ2 Θ0 mrg. inv mrg.
  have[Θ4[fr0 mrg]]:=ih _ _ H3.
    exists (m0 :U Θ4). split...
  have[Θ4[fr0 mrg]]:=ih _ _ H3.
    exists (m0 :L Θ4). split...
  have[Θ4[fr0 mrg]]:=ih _ _ H3.
    exists (m0 :L Θ4). split...
  have[Θ4[fr0 mrg]]:=ih _ _ H3.
    exists (_: Θ4). split...
Qed.

Lemma free_pure Θ Θ' m l : free Θ l m Θ' -> Θ |> U -> Θ' |> U.
Proof.
  elim=>//{Θ Θ' m l}.
  move=>Θ m l e k. inv k.
  move=>Θ Θ' m n l fr ih mrg. inv mrg.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma free_subset Θ Θ1 Θ2 Θ' Θ1' l m n :
  Θ1 ∘ Θ2 => Θ ->free Θ l m Θ' -> free Θ1 l n Θ1' ->  m = n /\ Θ1' ∘ Θ2 => Θ'.
Proof with eauto 6 using merge.
  move=>mrg. elim: mrg l m n Θ' Θ1'=>{Θ Θ1 Θ2}.
  move=>l m n G1 G2 fr. inv fr.
  move=>G1 G2 G m mrg ih l n x G3 G4 fr1 fr2.
  { have[e1 e2]:=merge_length mrg.
    inv fr1; inv fr2...
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
  move=>G1 G2 G m mrg ih l n x G3 G4 fr1 fr2.
  { have[e1 e2]:=merge_length mrg.
    inv fr1; inv fr2...
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
  move=>G1 G2 G m mrg ih l n x G3 G4 fr1 fr2.
  { have[e1 e2]:=merge_length mrg.
    inv fr1; inv fr2.
    move/free_length in H4.
    rewrite e1 in H4.
    rewrite ltnn in H4. inv H4.
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
  move=>G1 G2 G mrg ih l m n G3 G4 fr1 fr2.
  { inv fr1; inv fr2...
    have:=ih _ _ _ _ _ H4 H5.
    firstorder... }
Qed.

Lemma resolve_merge_pure Θ1 Θ2 Θ A A' :
  resolve Θ1 A A' -> Θ1 ∘ Θ2 => Θ -> Θ2 |> U -> resolve Θ A A'.
Proof with eauto using
  resolve, merge_pure_pure, key, resolve_wkU, resolve_wkN.
  move=>rsA. move: Θ1 A A' rsA Θ2 Θ.
  apply: resolve_ind_nested...
  move=>Θ A A' m m' s t k1 rsA ihA rsm ihm Θ2 Θ0 mrg k2.
  { constructor...
    destruct t...
    apply: key_impure.
    have[e1[e2 e3]]:=merge_re_re mrg.
    apply: ihA.
    rewrite<-e2.
    apply: merge_re_id.
    apply: re_pure. }
  move=>Θ1 Θ2 Θ m m' n n' mrg1 rsm ihm rsn ihn Θ0 Θ3 mrg2 k.
  { have[G[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm; eauto.
    eauto. }
  move=>Θ1 A A' Cs Cs' s k1 rA ihA rCs ihCs Θ2 Θ mrg k2.
  { have e:=merge_pureL mrg k1; subst.
    have e:=merge_pureR mrg k2; subst.
    constructor... }
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg1 rm ihm rQ ihQ rFs ihFs G1 G2 mrg2 k.
  { have e:=merge_pureR mrg2 k; subst.
    apply: resolve_case.
    apply: mrg1.
    all: eauto. }
  move=>Θ Θ' l m m' fr rm ihm G1 G2 mrg k.
  { have e:=merge_pureR mrg k; subst.
    econstructor... }
Qed.


Lemma resolve_free Θ1 Θ2 Θ Θ' l m n :
  free Θ l n Θ' -> resolve Θ1 (Ptr l) m -> Θ1 ∘ Θ2 => Θ ->
  exists Θ1', Θ1' ∘ Θ2 => Θ' /\ resolve Θ1' n m.
Proof with eauto using merge.
  intros.
  inv H0.
  have [e mrg]:=free_subset H1 H H3; subst.
  exists Θ'0.
  split...
Qed.

Inductive nf : nat -> term -> Prop :=
| nf_var i x :
  x < i ->
  nf i (Var x)
| nf_sort i s l :
  nf i (s @ l)
| nf_pi i A B s r t :
  nf i A ->
  nf i.+1 B ->
  nf i (Pi A B s r t)
| nf_lam i A m s t :
  nf i A ->
  nf i.+1 m ->
  nf i (Lam A m s t)
| nf_app i m n :
  nf i m ->
  nf i n ->
  nf i (App m n)
| nf_indd i A Cs s :
  nf i A ->
  All1 (nf i.+1) Cs ->
  nf i (Ind A Cs s)
| nf_constr i x I s :
  nf i I ->
  nf i (Constr x I s)
| nf_case i m Q Fs :
  nf i m ->
  nf i Q ->
  All1 (nf i) Fs ->
  nf i (Case m Q Fs)
| nf_fix i A m :
  nf i A ->
  nf i.+1 m ->
  nf i (Fix A m)
| nf_ptr i l :
  nf i (Ptr l).

Section nf_ind_nested.
  Variable P : nat -> term -> Prop.
  Hypothesis ih_var :
    forall i x, x < i -> P i (Var x).
  Hypothesis ih_sort :
    forall i s l, P i (s @ l).
  Hypothesis ih_pi :
    forall i A B s r t,
      nf i A -> P i A ->
      nf i.+1 B -> P i.+1 B ->
      P i (Pi A B s r t).
  Hypothesis ih_lam :
    forall i A m s t,
      nf i A -> P i A ->
      nf i.+1 m -> P i.+1 m ->
      P i (Lam A m s t).
  Hypothesis ih_app :
    forall i m n,
      nf i m -> P i m ->
      nf i n -> P i n ->
      P i (App m n).
  Hypothesis ih_indd :
    forall i A Cs s,
      nf i A -> P i A ->
      All1 (nf i.+1) Cs -> All1 (P i.+1) Cs ->
      P i (Ind A Cs s).
  Hypothesis ih_constr :
    forall i x I s,
      nf i I -> P i I ->
      P i (Constr x I s).
  Hypothesis ih_case :
    forall i m Q Fs,
      nf i m -> P i m ->
      nf i Q -> P i Q ->
      All1 (nf i) Fs -> All1 (P i) Fs ->
      P i (Case m Q Fs).
  Hypothesis ih_fix :
    forall i A m,
      nf i A -> P i A ->
      nf i.+1 m -> P i.+1 m ->
      P i (Fix A m).
  Hypothesis ih_ptr :
    forall i l, P i (Ptr l).

  Fixpoint nf_ind_nested
    i m (pf : nf i m) : P i m.
  Proof.
    case pf; intros.
    apply: ih_var; eauto.
    apply: ih_sort; eauto.
    apply: ih_pi; eauto.
    apply: ih_lam; eauto.
    apply: ih_app; eauto.
    have ih_nested:=
      fix fold i Cs (pf : All1 (nf i) Cs) : All1 (P i) Cs :=
        match pf with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (nf_ind_nested _ _ hd) (fold _ _ tl)
        end; eauto.
    apply: ih_constr; eauto.
    have ih_nested:=
      fix fold i Fs (pf : All1 (nf i) Fs) : All1 (P i) Fs :=
        match pf with
        | All1_nil => All1_nil _
        | All1_cons _ _ hd tl =>
          All1_cons (nf_ind_nested _ _ hd) (fold _ _ tl)
        end; eauto.
    apply: ih_fix; eauto.
    apply: ih_ptr; eauto.
  Qed.
End nf_ind_nested.

Inductive all_ptr : list term -> Prop :=
| all_ptr_nil : all_ptr nil
| all_ptr_cons l ms :
  all_ptr ms -> all_ptr (Ptr l :: ms).

Inductive wr_env : context term -> Prop :=
| wr_nil : wr_env nil
| wr_sort Θ s i :
  wr_env Θ ->
  wr_env (s @ i :U Θ)
| wr_pi Θ A B s r t :
  nf 0 A ->
  nf 1 B ->
  wr_env Θ ->
  wr_env (Pi A B s r t :U Θ)
| wr_lam Θ A m s t :
  nf 0 A ->
  nf 1 m ->
  wr_env Θ ->
  wr_env (Lam A m s t :{t} Θ)
| wr_indd Θ A Cs s ms :
  nf 0 A ->
  All1 (nf 1) Cs ->
  All1 (nf 0) ms ->
  wr_env Θ ->
  wr_env (spine (Ind A Cs s) ms :U Θ)
| wr_constr Θ i I s ms :
  nf 0 I ->
  all_ptr ms ->
  wr_env Θ ->
  wr_env (spine (Constr i I s) ms :{s} Θ)
| wr_fix Θ A m :
  nf 0 A ->
  nf 1 m ->
  wr_env Θ ->
  wr_env (Fix A m :U Θ)
| wr_N Θ :
  wr_env Θ ->
  wr_env (_: Θ).

Lemma nf_typing_All2i (Γ : context term) Fs Cs s i :
  All2i
    (fun _ F C =>
       constr 0 s C ∧ nf (length Γ) F) i Fs Cs ->
  All1 (nf (length Γ)) Fs.
Proof with eauto using All1.
  elim=>{Fs Cs i}...
  move=>i F F' Fs Fs' [_ h] hd tl.
  constructor...
Qed.

Lemma nf_typing Γ m A s :
  Γ ⊢ m : A : s -> nf (length Γ) m.
Proof with eauto using nf.
  move:Γ m A s. apply: clc_type_ind_nested=>//=...
  move=>Γ A B [|] r t i k tyA ihA tyB ihB.
  { constructor...
    rewrite re_length... }
  { constructor...
    rewrite re_length... }
  move=>Γ x A s hs.
  { constructor.
    apply: has_length... }
  move=>Γ A B m s r t i k tyP nfP tym nfm.
  { inv nfP.
    constructor...
    rewrite re_length... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn.
  { have[e1 e2]:=merge_length mrg.
    constructor.
    rewrite<-e1...
    rewrite<-e2... }
  move=>Γ1 Γ2 Γ A Q s s' k Fs Cs m ms leq ar key mrg
    tym ihm tyQ ihQ tyFs ihFs.
  { have[e1 e2]:=merge_length mrg.
    constructor.
    rewrite<-e1...
    rewrite<-e2.
    rewrite re_length...
    rewrite<-e2.
    apply: nf_typing_All2i... }
Qed.

Lemma wr_env_re Θ : wr_env Θ -> wr_env [Θ].
Proof with eauto using wr_env.
  elim=>{Θ}...
  move=>Θ A m s [|] nfA nfm wr ih//=...
  move=>Θ lm ln [|] wr ih//=...
Qed.

Lemma nf_spine' i h ms :
  nf i h -> All1 (nf i) ms -> nf i (spine' h ms).
Proof.
  elim: ms i h=>//=.
  move=>m ms ih i h hd tl. inv tl.
  constructor; eauto.
Qed.

Lemma All1_nf_append i ms ms' :
  All1 (nf i) ms -> All1 (nf i) ms' ->
  All1 (nf i) (ms ++ ms').
Proof with eauto using All1.
  move=>nfms. elim: nfms ms'=>//={ms}...
Qed.

Lemma All1_nf_rev i ms :
  All1 (nf i) ms -> All1 (nf i) (rev ms).
Proof with eauto using All1.
  elim=>//={ms}...
  move=>m ms nfm hd tl.
  replace (m :: ms) with ([:: m] ++ ms) by eauto.
  rewrite rev_cat.
  apply: All1_nf_append...
Qed.

Lemma nf_spine i h ms :
  nf i h -> All1 (nf i) ms -> nf i (spine h ms).
Proof.
  move=>nfh nfms.
  rewrite spine_spine'_rev.
  apply: nf_spine'; eauto.
  apply: All1_nf_rev; eauto.
Qed.

Lemma all_ptr_nf ms i :
  all_ptr ms -> All1 (nf i) ms.
Proof with eauto using All1, nf. elim=>{ms}... Qed.

Lemma free_wr_nf Θ l m Θ' :
  free Θ l m Θ' -> wr_env Θ -> nf 0 m.
Proof with eauto using nf.
  elim=>//{Θ l m Θ'}.
  move=>Θ m l e wr. inv wr...
  { apply: nf_spine... }
  { apply: nf_spine...
    apply: all_ptr_nf... }
  move=>Θ m l e wr. inv wr...
  { apply: nf_spine...
    apply: all_ptr_nf... }
  move=>Θ Θ' m n l fr ih wr. inv wr...
Qed.

Lemma wr_merge Θ1 Θ2 Θ :
  Θ1 ∘ Θ2 => Θ -> wr_env Θ1 -> wr_env Θ2 -> wr_env Θ.
Proof with eauto using wr_env.
  elim=>{Θ1 Θ2 Θ}...
  move=>Θ1 Θ2 Θ m mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
  move=>Θ1 Θ2 Θ m mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
  move=>Θ1 Θ2 Θ m mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
  move=>Θ1 Θ2 Θ mrg ih wr1 wr2.
  inv wr1; inv wr2; constructor...
Qed.

Lemma wr_merge_inv Θ1 Θ2 Θ :
  Θ1 ∘ Θ2 => Θ -> wr_env Θ -> wr_env Θ1 /\ wr_env Θ2.
Proof with eauto using wr_env.
  elim...
  move=>Γ1 Γ2 Γ m mrg ih wr. inv wr.
    move:H0=>/ih[wr1 wr2]...
    move:H3=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
    move:H3=>/ih[wr1 wr2]...
  move=>Γ1 Γ2 Γ m mrg ih wr. inv wr.
    move:H4=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
  move=>Γ1 Γ2 Γ m mrg ih wr. inv wr.
    move:H4=>/ih[wr1 wr2]...
    move:H4=>/ih[wr1 wr2]...
  move=>Γ1 Γ2 Γ mrg ih wr. inv wr.
    move:H0=>/ih[wr1 wr2]...
Qed.

Lemma free_wr Θ Θ' l m :
  free Θ l m Θ' -> wr_env Θ -> wr_env Θ'.
Proof with eauto using wr_env.
  elim=>{Θ l m Θ'}; eauto.
  move=>Θ m l e wr. inv wr...
  move=>Θ Θ' m n l fr ih wr.
  inv wr...
Qed.

Lemma nf_weaken i j m : nf i m -> i <= j -> nf j m.
Proof with eauto using nf, All1.
  move=>nfm. move: i m nfm j.
  apply: nf_ind_nested...
  move=>i x l1 j l2.
  { constructor.
    apply: leq_trans... }
  move=>i A Cs s nfA ihA nfCs ihCs j leq.
  { constructor...
    elim: ihCs... }
  move=>i m Q Fs nfm ihm nfQ ihQ nfFs ihFs j leq.
  { constructor...
    elim: ihFs... }
Qed.

Lemma resolve_wr_nfi Θ m m' i :
  resolve Θ m m' -> wr_env Θ -> nf i m' -> nf i m.
Proof with eauto using nf, wr_env_re, All1.
  move=>rm. move: Θ m m' rm i.
  apply: resolve_ind_nested...
  move=>Θ A A' B B' s r t k rA ihA rB ihB i wr nfP. inv nfP...
  move=>Θ A A' m m' s t k rA ihA rm ihm i wr nfL. inv nfL...
  move=>Θ1 Θ2 Θ m m' n n' mrg rm ihm rn ihn i wr nfA.
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfA... }
  move=>Θ A A' Cs Cs' s k rA ihA _ ihCs i wr nfI.
  { inv nfI. constructor...
    elim: ihCs H4=>{Cs Cs'}...
    move=>C C' Cs Cs' h hd ih tl. inv tl... }
  move=>Θ i I I' s k rI ihI x wr nfC. inv nfC...
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg
    rm ihm rQ ihQ rFs ihFs i wr nfC. inv nfC.
  { have[wr1 wr2]:=wr_merge_inv mrg wr.
    constructor...
    elim: ihFs H5=>{Fs Fs' rFs}...
    move=>F F' Fs Fs' h hd ih tl. inv tl... }
  move=>Θ A A' m m' k rA ihA rm ihm i wr nfF. inv nfF...
Qed.

Lemma resolve_wr_nfi' Θ m m' i :
  resolve Θ m m' -> wr_env Θ -> nf i m -> nf i m'.
Proof with eauto using nf, wr_env_re, All1.
  move=>rm. move: Θ m m' rm i.
  apply: resolve_ind_nested...
  move=>Θ A A' B B' s r t k rA ihA rB ihB i wr nfP. inv nfP...
  move=>Θ A A' m m' s t k rA ihA rm ihm i wr nfL. inv nfL...
  move=>Θ1 Θ2 Θ m m' n n' mrg rm ihm rn ihn i wr nfA.
  { have[wr1 wr2]:=wr_merge_inv mrg wr. inv nfA... }
  move=>Θ A A' Cs Cs' s k rA ihA _ ihCs i wr nfI.
  { inv nfI. constructor...
    elim: ihCs H4=>{Cs Cs'}...
    move=>C C' Cs Cs' h hd ih tl. inv tl... }
  move=>Θ i I I' s k rI ihI x wr nfC. inv nfC...
  move=>Θ1 Θ2 Θ m m' Q Q' Fs Fs' mrg
    rm ihm rQ ihQ rFs ihFs i wr nfC. inv nfC.
  { have[wr1 wr2]:=wr_merge_inv mrg wr.
    constructor...
    elim: ihFs H5=>{Fs Fs' rFs}...
    move=>F F' Fs Fs' h hd ih tl. inv tl... }
  move=>Θ A A' m m' k rA ihA rm ihm i wr nfF. inv nfF...
  move=>Θ Θ' l m m' fr rs ih i wr nfP.
  { apply: ih...
    apply: free_wr...
    have n:=free_wr_nf fr wr.
    apply: nf_weaken... }
Qed.

Lemma free_wr_ptr Θ Θ' l i :
  free Θ l (Ptr i) Θ' -> wr_env Θ -> False.
Proof.
  move e:(Ptr i)=>m fr. elim: fr i e=>{Θ Θ' l m}.
  move=>Θ m l e1 i e2 wr; subst. inv wr.
  { solve_spine. }
  { solve_spine. }
  move=>Θ m l e1 i e2 wr; subst. inv wr.
  { solve_spine. }
  move=>Θ Θ' m n l fr ih i e wr; subst.
  inv wr; apply: ih; eauto.
Qed.

Lemma free_wr_sort Θ Θ' l s i :
  free Θ l (s @ i) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(s @ i)=>m fr. elim: fr s i e=>//{Θ Θ' l m}.
  move=>Θ m l e1 s i e2 wr; subst. inv wr.
  { exfalso. solve_spine. }
  move=>Θ Θ' m n l fr ih s i e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_pi Θ Θ' l A B s r t :
  free Θ l (Pi A B s r t) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Pi A B s r t)=>m fr. elim: fr A B s r t e=>//{Θ Θ' l m}.
  move=>Θ m l e1 A B s r t e2 wr; subst. inv wr.
  { exfalso. solve_spine. }
  move=>Θ Θ' m n l fr ih A B s r t e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_var Θ Θ' l x :
  free Θ l (Var x) Θ' -> wr_env Θ -> False.
Proof.
  move e:(Var x)=>m fr. elim: fr x e=>//{Θ Θ' l m}.
  move=>Θ m l e1 x e2 wr; subst. inv wr.
  { solve_spine. }
  { solve_spine. }
  move=>Θ m l e1 x e2 wr; subst. inv wr.
  { solve_spine. }
  move=>Θ Θ' m n l fr ih x e wr; subst.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_lam Θ Θ' l A m s :
  free Θ l (Lam A m s U) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Lam A m s U)=>n fr. elim: fr A m s e=>//{Θ Θ' l n}.
  move=>Θ m l e1 A n s e2 wr; subst. inv wr. inv H4.
  { solve_spine. }
  move=>Θ Θ' m n l fr ih A n0 s e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma ind_constr_spine' A I Cs i s t ms1 ms2 :
  spine' (Constr i I t) ms1 <> spine' (Ind A Cs s) ms2.
Proof.
  elim: ms1 ms2=>//=.
  move=>[|m ms]//=.
  move=>m1 ms1 ih [|m2 ms2]//=.
  move=>[/ih]//.
Qed.

Lemma ind_constr_spine A I Cs i s t ms1 ms2 :
  spine (Constr i I t) ms1 <> spine (Ind A Cs s) ms2.
Proof.
  rewrite!spine_spine'_rev.
  apply: ind_constr_spine'.
Qed.

Lemma free_wr_ind Θ Θ' l A Cs s ms :
  free Θ l (spine (Ind A Cs s) ms) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(spine (Ind A Cs s) ms)=>n fr.
  elim: fr A Cs s ms e=>//{Θ Θ' l n}.
  move=>Θ m l e1 A Cs s ms e2 wr; subst. inv wr.
  { exfalso. solve_spine. }
  { exfalso.
    apply: ind_constr_spine; eauto. }
  move=>Θ Θ' m n l fr ih A Cs s ms e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma constr_constr_spine' i1 i2 I1 I2 s1 s2 ms1 ms2 :
  s1 <> s2 -> spine' (Constr i1 I1 s1) ms1 <> spine' (Constr i2 I2 s2) ms2.
Proof.
  elim: ms1 ms2=>//=.
  move=>[|m ms]//=neq [e1 e2 e3]//.
  move=>m1 ms1 ih [|m2 ms2] neq//=.
  move=>[/ih]//.
Qed.

Lemma constr_constr_spine i1 i2 I1 I2 s1 s2 ms1 ms2 :
  s1 <> s2 -> spine (Constr i1 I1 s1) ms1 <> spine (Constr i2 I2 s2) ms2.
Proof.
  rewrite!spine_spine'_rev.
  apply: constr_constr_spine'.
Qed.

Lemma free_wr_constr Θ Θ' l i I ms :
  free Θ l (spine (Constr i I U) ms) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(spine (Constr i I U) ms)=>n fr.
  elim: fr i I ms e=>//{Θ Θ' l n}.
  move=>Θ m l e1 i I ms e2 wr; subst. inv wr.
  { exfalso. solve_spine. }
  { exfalso. apply: constr_constr_spine; eauto.
    move=>h. inv h. }
  move=>Θ Θ' m n l fr ih i I ms e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.

Lemma free_wr_fix Θ Θ' l A m :
  free Θ l (Fix A m) Θ' -> wr_env Θ -> Θ = Θ'.
Proof.
  move e:(Fix A m)=>n fr. elim: fr A m e=>//{Θ Θ' l n}.
  move=>Θ m l e1 A n e2 wr; subst. inv wr.
  { exfalso. solve_spine. }
  move=>Θ Θ' m n l fr ih A m0 e wr; subst.
  f_equal.
  apply: ih; eauto.
  inv wr; eauto.
Qed.
