From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context clc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort s l :
  pstep (s @ l) (s @ l)
| pstep_lam A A' n n' s t : 
  pstep A A' -> 
  pstep n n' -> 
  pstep (Lam A n s t) (Lam A' n' s t)
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta A m m' n n' s t :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam A m s t) n) (m'.[n'/])
| pstep_pi A A' B B' s t :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi A B s t) 
        (Pi A' B' s t).

Definition sred σ τ :=
  forall x : var, (σ x) ~>* (τ x).

Lemma step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using step.
  move=> A m n s t σ. 
  replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
  apply step_beta. autosubst.
Qed.

Lemma red_app m m' n n' :
  m ~>* m' -> n ~>* n' -> App m n ~>* App m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App m' n)).
  apply: (star_hom (App^~ n)) r1=>x y. exact: step_appL.
  apply: star_hom r2. exact: step_appR.
Qed.

Lemma red_lam A A' m m' s t :
  A ~>* A' -> m ~>* m' -> Lam A m s t ~>* Lam A' m' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam A' m s t)).
  apply: (star_hom (((Lam^~ m)^~ s)^~ t)) r1=>x y. exact: step_lamL.
  apply: (star_hom (((Lam A')^~ s)^~ t)) r2=>x y. exact: step_lamR.
Qed.

Lemma red_pi A A' B B' s t :
  A ~>* A' -> B ~>* B' -> Pi A B s t ~>* Pi A' B' s t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi A' B s t)).
  apply: (star_hom (((Pi^~ B)^~ s)^~ t)) r1=>x y. exact: step_piL.
  apply: (star_hom (((Pi A')^~ s)^~ t)) r2=>x y. exact: step_piR.
Qed.

Lemma red_subst m n σ : m ~>* n -> m.[σ] ~>* n.[σ].
Proof.
  move=>st.
  elim: st σ=>{n}; eauto.
  move=> n n' r ih st σ.
  move:(ih σ)=>{}ih.
  move:(step_subst σ st)=>r'.
  apply: star_trans.
  apply: ih.
  by apply: star1.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: red_subst. exact: A. Qed.

Hint Resolve red_app red_lam red_pi sred_up : red_congr.

Lemma red_compat σ τ s : sred σ τ -> red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with red_congr. Qed.

Definition sconv (σ τ : var -> term) :=
  forall x, σ x === τ x.

Lemma conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (App m' n)).
  apply: (conv_hom (App^~ n)) r1=>x y. exact: step_appL.
  apply: conv_hom r2. exact: step_appR.
Qed.

Lemma conv_lam A A' m m' s t :
  A === A' -> m === m' -> Lam A m s t === Lam A' m' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam A' m s t)).
  apply: (conv_hom (((Lam^~ m)^~ s)^~ t)) r1=>x y. exact: step_lamL.
  apply: (conv_hom (((Lam A')^~ s)^~ t)) r2=>x y. exact: step_lamR.
Qed.

Lemma conv_pi A A' B B' s t :
  A === A' -> B === B' -> Pi A B s t === Pi A' B' s t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi A' B s t)).
  apply: (conv_hom (((Pi^~ B)^~ s)^~ t)) r1=>x y. exact: step_piL.
  apply: (conv_hom (((Pi A')^~ s)^~ t)) r2=>x y. exact: step_piR.
Qed.

Lemma conv_subst σ s t : 
  s === t -> s.[σ] === t.[σ].
Proof. 
  move=>c.
  apply: conv_hom c.
  exact: step_subst.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Lemma conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof.
  elim: s σ τ => *; asimpl; eauto using
    conv_app, conv_lam, conv_pi, sconv_up.
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep n n' : step n n' -> pstep n n'.
Proof with eauto using pstep, pstep_refl. elim... Qed.

Lemma pstep_red s t : pstep s t -> s ~>* t.
Proof.
  elim=> {s t} //=; eauto with red_congr.
  move=> A m m' n n' s t p1 r1 p2 r2. eapply starES. by econstructor.
  apply: (star_trans (m'.[n.:Var])). exact: red_subst.
  by apply: red_compat => -[|].
Qed.

Lemma pstep_subst s t σ : pstep s t -> pstep s.[σ] t.[σ].
Proof with eauto using pstep, pstep_refl.
  move=>ps.
  elim: ps σ=>{s t}...
  move=>A m m' n n' s t ps1 ih1 ps2 ih2 σ.
  asimpl.
  specialize (ih1 (up σ)).
  specialize (ih2 σ).
  pose (pstep_beta A.[σ] s t ih1 ih2).
  by asimpl in p.
Qed.

Definition psstep (σ τ : var -> term) := 
  forall x, pstep (σ x) (τ x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat s t σ τ :
  pstep s t -> psstep σ τ -> pstep s.[σ] t.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=> ps. elim: ps σ τ=>{s t}...
  move=> A m m' n n' s t ps1 ih1 ps2 ih2 σ τ pss.
  asimpl.
  pose (ih1 _ _ (psstep_up pss)).
  pose (ih2 _ _ pss).
  pose (pstep_beta A.[σ] s t p p0).
  by asimpl in p1.
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat.
  move...
Qed.

Lemma pstep_compat_beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat.
  move...
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 ->
    exists2 m', pstep m1 m' & pstep m2 m'.
Proof with eauto using pstep, pstep_refl, pstep_compat_beta.
  move=>ps. elim: ps m2=>{m m1}.
  move=> x m2 p.
    inv p.
    exists (Var x)...
  move=> s l m2 p.
    inv p.
    exists (s @ l)...
  move=> A A' n n' s t pA ihA pn ihn m2 p.
    inv p.
    move: (ihA _ H4)=>[A0 pA1 pA2].
    move: (ihn _ H5)=>[n0 pn1 pn2].
    exists (Lam A0 n0 s t)...
  move=> m m' n n' pm ihm pn ihn m2 p.
    inv p.
    move: (ihm _ H1)=>[m0 pm1 pm2].
    move: (ihn _ H3)=>[n0 pn1 pn2].
    exists (App m0 n0)...
    inv pm.
    move: (ihn _ H3)=>[n0 pn1 pn2].
    have pL : pstep (Lam A m0 s t) (Lam A' m'0 s t)...
    move: (ihm _ pL)=>[x px1 px2].
    inv px1. inv px2.
    exists (n'2.[n0/])...
  move=> A m m' n n' s t pm ihm pn ihn m2 p.
    inv p. inv H1.
    move: (ihm _ H7)=>[mx pm1 pm2].
    move: (ihn _ H3)=>[nx pn1 pn2].
    exists (mx.[nx/])...
    move: (ihm _ H5)=>[mx pm1 pm2].
    move: (ihn _ H6)=>[nx pn1 pn2].
    exists (mx.[nx/])...
  move=> A A' B B' s t pA ihA pB ihB m2 p.
    inv p.
    move: (ihA _ H4)=>[Ax pA1 pA2].
    move: (ihB _ H5)=>[Bx pB1 pB2].
    exists (Pi Ax Bx s t)...
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> m ~>* m2 -> exists2 m', m1 ~>* m' & pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>m1 m2 r1 ih /step_pstep p1 m' p2.
  move:(ih _ p2)=>[m3 r2 p3].
  move:(pstep_diamond p1 p3)=>[m4 p4 p5].
  exists m4...
  apply: star_trans.
  apply: r2.
  by apply: pstep_red.
Qed.

Theorem confluence :
  confluent step.
Proof with eauto using step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r.
  elim: r z=>{y}.
  move=>z r. exists z...
  move=>y z r1 ih /step_pstep p z0 /ih[z1 r2 r3].
  move:(strip p r2)=>[z2 r4 p1].
  exists z2...
  apply: star_trans.
  apply r3.
  apply: pstep_red...
Qed.

Theorem church_rosser :
  CR step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma red_sort_inv s l A :
  s @ l ~>* A -> A = s @ l.
Proof.
  elim=>//y z r1 e r2; subst.
  inv r2.
Qed.

Lemma red_pi_inv A B s t x :
  Pi A B s t ~>* x -> 
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi A' B' s t.
Proof.
  elim.
  exists A. exists B. repeat constructor.
  move=> y z r [A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma red_var_inv x y : Var x ~>* y -> y = Var x.
Proof.
  elim=>//{y} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma red_lam_inv A m n s t :
  Lam A m s t ~>* n ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ n = Lam A' m' s t.
Proof.
  elim.
  exists A. exists m. repeat constructor.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  s1 @ l1 === s2 @ l2 -> s1 = s2 /\ l1 = l2.
Proof.
  move/church_rosser=>[x/red_sort_inv->/red_sort_inv[->->]]//.
Qed.

Lemma pi_inj A A' B B' s s' t t' :
  Pi A B s t === Pi A' B' s' t' -> 
    A === A' /\ B === B' /\ s = s' /\ t = t'.
Proof.
  move/church_rosser=>
    [x/red_pi_inv[A1[B1[rA1[rB1->]]]]
      /red_pi_inv[A2[B2[rA2[rB2[]]]]]] eA eB es et; subst.
  repeat split.
  apply: conv_trans.
    apply: star_conv. by apply: rA1.
    apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
    apply: star_conv. by apply: rB1.
    apply: conv_sym. by apply: star_conv.
Qed.

Ltac red_inv m H :=
  match m with
  | Var   => apply red_var_inv in H
  | Sort  => apply red_sort_inv in H
  | Pi    => apply red_pi_inv in H
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
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  end; eauto.