From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export clc_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~>> n" (at level 30).
Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  Var x ~>> Var x
| pstep_sort s :
  Sort s ~>> Sort s
| pstep_lam A A' n n' s : 
  A ~>> A' -> 
  n ~>> n' -> 
  Lam A n s ~>> Lam A' n' s
| pstep_app m m' n n' :
  m ~>> m' ->
  n ~>> n' ->
  App m n ~>> App m' n'
| pstep_beta A m m' n n' s :
  m ~>> m' ->
  n ~>> n' ->
  App (Lam A m s) n ~>> m'.[n'/]
| pstep_fix A A' m m' :
  A ~>> A' ->
  m ~>> m' ->
  Fix A m ~>> Fix A' m'
| pstep_iota0 A A' m m' :
  A ~>> A' ->
  m ~>> m' ->
  Fix A m ~>> m'.[Fix A' m'/]
| pstep_pi A A' B B' s :
  A ~>> A' ->
  B ~>> B' ->
  Pi A B s ~>> Pi A' B' s
| pstep_unit :
  Unit ~>> Unit
| pstep_it :
  It ~>> It
| pstep_either :
  Either ~>> Either
| pstep_left :
  Left ~>> Left
| pstep_right :
  Right ~>> Right
| pstep_sigma A A' B B' s :
  A ~>> A' ->
  B ~>> B' ->
  Sigma A B s ~>> Sigma A' B' s
| pstep_pair m m' n n' t :
  m ~>> m' ->
  n ~>> n' ->
  Pair m n t ~>> Pair m' n' t
| pstep_case m m' n1 n1' n2 n2' :
  m ~>> m' ->
  n1 ~>> n1' ->
  n2 ~>> n2' ->
  Case m n1 n2 ~>> Case m' n1' n2'
| pstep_iotaL n1 n1' n2 :
  n1 ~>> n1' ->
  Case Left n1 n2 ~>> n1'
| pstep_iotaR n1 n2 n2' :
  n2 ~>> n2' ->
  Case Right n1 n2 ~>> n2'
| pstep_letin1 m m' n n' :
  m ~>> m' ->
  n ~>> n' ->
  LetIn1 m n ~>> LetIn1 m' n'
| pstep_iota1 n n' :
  n ~>> n' ->
  LetIn1 It n ~>> n'
| pstep_letin2 m m' n n' :
  m ~>> m' ->
  n ~>> n' ->
  LetIn2 m n ~>> LetIn2 m' n'
| pstep_iota2 m1 m1' m2 m2' n n' t :
  m1 ~>> m1' ->
  m2 ~>> m2' ->
  n ~>> n' ->
  LetIn2 (Pair m1 m2 t) n ~>> n'.[m2',m1'/]
| pstep_main :
  Main ~>> Main
| pstep_proto :
  Proto ~>> Proto
| pstep_stop r :
  Stop r ~>> Stop r
| pstep_act r A A' B B' :
  A ~>> A' ->
  B ~>> B' ->
  Act r A B ~>> Act r A' B'
| pstep_ch r A A' :
  A ~>> A' ->
  Ch r A ~>> Ch r A'
| pstep_fork m m' n n' :
  m ~>> m' ->
  n ~>> n' ->
  Fork m n ~>> Fork m' n'
| pstep_recv ch ch' :
  ch ~>> ch' ->
  Recv ch ~>> Recv ch'
| pstep_send ch ch' :
  ch ~>> ch' ->
  Send ch ~>> Send ch'
| pstep_close ch ch' :
  ch ~>> ch' ->
  Close ch ~>> Close ch'
| pstep_wait ch ch' :
  ch ~>> ch' ->
  Wait ch ~>> Wait ch'
where "m ~>> n" := (pstep m n).

Notation pred := (star pstep).
Notation "m ~>>* n" := (pred m n) (at level 30).
Notation "m === n" := (conv pstep m n) (at level 50).

Lemma pstep_refl m : m ~>> m.
Proof. elim: m; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep m n : m ~> n -> m ~>> n.
Proof with eauto using pstep. elim... Qed.
Hint Resolve step_pstep.

Lemma pstep_subst m n σ : m ~>> n -> m.[σ] ~>> n.[σ].
Proof with eauto using pstep.
  move=>ps. elim: ps σ=>{m n}...
  { move=>A m m' n n' s pm ihm pn ihn σ. asimpl.
    specialize (ihm (up σ)).
    specialize (ihn σ).
    pose proof (pstep_beta A.[σ] s ihm ihn).
    by asimpl in H. }
  { move=>A A' m m' pA ihA tym ihm σ. asimpl.
    replace (m'.[Fix A'.[σ] m'.[up σ] .: σ])
      with (m'.[up σ].[Fix A'.[σ] m'.[up σ]/])
      by autosubst.
    constructor... }
  { move=>m1 m1' m2 m2' n n' t pm1 ihm1 pm2 ihm2 pn ihn σ. asimpl.
    specialize (ihm1 σ).
    specialize (ihm2 σ).
    specialize (ihn (upn 2 σ)).
    pose proof (pstep_iota2 t ihm1 ihm2 ihn).
    by asimpl in H. }
Qed.

Definition psstep (σ τ : var -> term) := forall x, σ x ~>> τ x.

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma psstep_upn n σ τ : psstep σ τ -> psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  { move=>σ τ pss. by asimpl. }
  { move=>n ihn σ τ/ihn/psstep_up. by asimpl. }
Qed.

Lemma pstep_compat m n σ τ :
  m ~>> n -> psstep σ τ -> m.[σ] ~>> n.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=>ps. elim: ps σ τ=>{m n}...
  { move=>A m m' n n' s pm ihm pn ihn σ τ pss. asimpl.
    have{}ihm:=ihm _ _ (psstep_up pss).
    have{}ihn:=ihn _ _ pss.
    pose proof (pstep_beta A.[σ] s ihm ihn).
    by asimpl in H. }
  { move=>A A' m m' pA ihA pm ihm σ τ pss. asimpl.
    have{}ihA:=ihA _ _ pss.
    have{}ihm:=ihm _ _ (psstep_up pss).
    replace (m'.[Fix A'.[τ] m'.[up τ] .: τ])
      with (m'.[up τ].[Fix A'.[τ] m'.[up τ]/])
      by autosubst... }
  { move=>m1 m1' m2 m2' n n' t pm1 ihm1 pm2 ihm2 pn ihn σ τ pss. asimpl.
    have{}ihm1:=ihm1 _ _ pss.
    have{}ihm2:=ihm2 _ _ pss.
    have{}ihn:=ihn _ _ (psstep_upn 2 pss).
    pose proof (pstep_iota2 t ihm1 ihm2 ihn).
    by asimpl in H. }
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> s1 ~>> s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  n ~>> n' -> m.[n/] ~>> m.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat. move... Qed.

Lemma pstep_compat_beta m m' n n' :
  m ~>> m' -> n ~>> n' -> m.[n/] ~>> m'.[n'/].
Proof with eauto using pstep_compat, psstep_refl, psstep_compat. move... Qed.

Lemma pstep_diamond m m1 m2 :
  m ~>> m1 -> m ~>> m2 ->
    exists2 m', m1 ~>> m' & m2 ~>> m'.
Proof with eauto 6 using 
  pstep, pstep_refl, 
  pstep_compat, pstep_compat_beta, 
  psstep_compat, psstep_refl.
  move=>ps. elim: ps m2=>{m m1}...
  { move=>A A' n n' s pA ihA pn ihn m2 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H3.
    have[nx pn1 pn2]:=ihn _ H4.
    exists (Lam Ax nx s)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[mx pm1 pm2]:=ihm _ H1.
      have[nx pn1 pn2]:=ihn _ H3.
      exists (App mx nx)... }
    { inv pm.
      have[nx pn1 pn2]:=ihn _ H3.
      have/ihm[x px1 px2]: Lam A m0 s ~>> Lam A' m'0 s...
      inv px1. inv px2.
      exists (n'2.[nx/])... } }
  { move=>A m m' n n' s pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[mx pm1 pm2]:=ihm _ H6.
      have[nx pn1 pn2]:=ihn _ H3.
      exists (mx.[nx/])... }
    { have[mx pm1 pm2]:=ihm _ H4.
      have[nx pn1 pn2]:=ihn _ H5.
      exists (mx.[nx/])... } }
  { move=>A A' m m' pA ihA pm ihm m2 p. inv p.
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... }
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... } }
  { move=>A A' m m' pA ihA pm ihm m2 p. inv p.
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... }
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... } }
  { move=>A A' B B' s pA ihA pB ihB m2 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H3.
    have[Bx pB1 pB2]:=ihB _ H4.
    exists (Pi Ax Bx s)... }
  { move=>A A' B B' s pA ihA pB ihB m2 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H3.
    have[Bx pB1 pB2]:=ihB _ H4.
    exists (Sigma Ax Bx s)... }
  { move=>m m' n n' t pm ihm pn ihn m2 p. inv p.
    have[mx pm1 pm2]:=ihm _ H3.
    have[nx pn1 pn2]:=ihn _ H4.
    exists (Pair mx nx t)... }
  { move=>m m' n1 n1' n2 n2' pm ihm pn1 ihn1 pn2 ihn2 m2 p. inv p.
    { have[mx pm1 pm2]:=ihm _ H2.
      have[nx pnx1 pnx2]:=ihn1 _ H4.
      have[ny pny1 pny2]:=ihn2 _ H5.
      exists (Case mx nx ny)... }
    { inv pm. have[nx pnx1 pnx2]:=ihn1 _ H3. exists nx... }
    { inv pm. have[ny pny1 pny2]:=ihn2 _ H3. exists ny... } }
  { move=>n1 n1' n2 pn ih m2 p. inv p.
    { inv H2. have[nx pn1 pn2]:=ih _ H4. exists nx... }
    { have[nx pn1 pn2]:=ih _ H2. exists nx... } }
  { move=>n1 n1' n2 pn ih m2 p. inv p.
    { inv H2. have[nx pn1 pn2]:=ih _ H5. exists nx... }
    { have[nx pn1 pn2]:=ih _ H2. exists nx... } }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[mx pm1 pm2]:=ihm _ H1.
      have[nx pn1 pn2]:=ihn _ H3.
      exists (LetIn1 mx nx)... }
    { inv pm. have[nx pn1 pn2]:=ihn _ H2. exists nx... } }
  { move=>n n' pn ihn m2 p. inv p.
    { inv H1. have[nx pn1 pn2]:=ihn _ H3. exists nx... }
    { have[nx pn1 pn2]:=ihn _ H0. exists nx... } }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[mx pm1 pm2]:=ihm _ H1.
      have[nx pn1 pn2]:=ihn _ H3.
      exists (LetIn2 mx nx)... }
    { inv pm.
      have/ihm[x px1 px2]:Pair m1 m0 t ~>> Pair m1' m2' t...
      have[nx pn1 pn2]:=ihn _ H4.
      inv px1. inv px2.
      exists (nx.[n'2,m'/])... } }
  { move=>m1 m1' m2 m2' n n' t pm1 ihm1 pm2 ihm2 pn ihn m0 p. inv p.
    { inv H1.
      have[mx pmx1 pmx2]:=ihm1 _ H5.
      have[my pmy1 pmy2]:=ihm2 _ H6.
      have[nx pn1 pn2]:=ihn _ H3.
      exists (nx.[my,mx/])... }
    { have[mx pmx1 pmx2]:=ihm1 _ H4.
      have[my pmy1 pmy2]:=ihm2 _ H5.
      have[nx pn1 pn2]:=ihn _ H6.
      exists (nx.[my,mx/])... } }
  { move=>r A A' B B' pA ihA pB ihB m2 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H3.
    have[Bx pB1 pB2]:=ihB _ H4.
    exists (Act r Ax Bx)... }
  { move=>r A A' pA ihA m2 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H2.
    exists (Ch r Ax)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    have[mx pm1 pm2]:=ihm _ H1.
    have[nx pn1 pn2]:=ihn _ H3.
    exists (Fork mx nx)... }
  { move=>ch ch' pc ih m2 p. inv p.
    have[x px1 px2]:=ih _ H0.
    exists (Recv x)... }
  { move=>ch ch' pc ih m2 p. inv p.
    have[x px1 px2]:=ih _ H0.
    exists (Send x)... }
  { move=>ch ch' pc ih m2 p. inv p.
    have[x px1 px2]:=ih _ H0.
    exists (Close x)... }
  { move=>ch ch' pc ih m2 p. inv p.
    have[x px1 px2]:=ih _ H0.
    exists (Wait x)... }
Qed.

Lemma strip m m1 m2 :
  m ~>> m1 -> m ~>>* m2 -> exists2 m', m1 ~>>* m' & m2 ~>> m'.
Proof with eauto using star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>y z r1 ih p1 m1 p2.
  have[x r2 p3]:=ih _ p2.
  have[w p4 p5]:=pstep_diamond p1 p3.
  exists w...
Qed.

Theorem confluence :
  confluent pstep.
Proof with eauto using pstep, star.
  unfold confluent.
  unfold joinable.
  move=>x y z r. elim: r z=>{y}.
  { move=>z r. exists z... }
  { move=>y z r1 ih p z0/ih[w r2 r3].
    have[v r4 p0]:=strip p r2.
    exists v... }
Qed.

Theorem church_rosser :
  CR pstep.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma pred_sort_inv s A :
  Sort s ~>>* A -> A = Sort s.
Proof with eauto.
  elim=>//y z r1 e r2; subst.
  inv r2...
Qed.

Lemma pred_pi_inv A B s x :
  Pi A B s ~>>* x ->
  exists A' B', A ~>>* A' /\ B ~>>* B' /\ x = Pi A' B' s.
Proof with eauto.
  elim=>{x}.
  { exists A. exists B... }
  {  move=>y z r[A'[B'[r1[r2 e]]]] p; subst. inv p.
     exists A'0. exists B'0.
     repeat split...
     apply: starSE...
     apply: starSE... }
Qed.

Lemma pred_var_inv x y : Var x ~>>* y -> y = Var x.
Proof with eauto.
  elim=>//{} y z r1 e r2; subst. inv r2...
Qed.

Lemma pred_lam_inv A m x s :
  Lam A m s ~>>* x ->
  exists A' m', A ~>>* A' /\ m ~>>* m' /\ x = Lam A' m' s.
Proof with eauto.
  elim=>{x}.
  { exists A. exists m... }
  { move=>y z r[A'[m'[r1[r2 e]]]]p; subst. inv p.
    exists A'0. exists n'.
    repeat split...
    apply: starSE...
    apply: starSE... }
Qed.

Lemma pred_unit_inv m : Unit ~>>* m -> m = Unit.
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_it_inv m : It ~>>* m -> m = It. 
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_either_inv m : Either ~>>* m -> m = Either.
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_left_inv m : Left ~>>* m -> m = Left.
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_right_inv m : Right ~>>* m -> m = Right.
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_sigma_inv A B s x :
  Sigma A B s ~>>* x ->
  exists A' B', A ~>>* A' /\ B ~>>* B' /\ x = Sigma A' B' s.
Proof with eauto.
  elim=>{x}.
  { exists A. exists B... }
  { move=>y z r[A'[B'[r1[r2 e]]]]p; subst. inv p.
    exists A'0. exists B'0.
    repeat split...
    apply: starSE...
    apply: starSE... }
Qed.

Lemma pred_pair_inv m n t x :
  Pair m n t ~>>* x ->
  exists m' n', m ~>>* m' /\ n ~>>* n' /\ x = Pair m' n' t.
Proof with eauto.
  elim=>{x}.
  { exists m. exists n... }
  { move=>y z r[m'[n'[r1[r2 e]]]]p; subst. inv p.
    exists m'0. exists n'0.
    repeat split...
    apply: starSE...
    apply: starSE... }
Qed.

Lemma pred_main_inv m : Main ~>>* m -> m = Main.
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_proto_inv n : Proto ~>* n -> n = Proto.
Proof. elim=>//y z r->p. by inv p. Qed.

Lemma pred_stop_inv r n : Stop r ~>>* n -> n = Stop r.
Proof with eauto.
  elim=>{n}...
  move=>y z rd e p; subst. inv p...
Qed.

Lemma pred_act_inv r A B x :
  Act r A B ~>>* x ->
  exists A' B',
    A ~>>* A' /\
    B ~>>* B' /\
    x = Act r A' B'.
Proof with eauto.
  elim=>{x}.
  { exists A. exists B... }
  { move=>y z rd[A'[B'[r1[r2 e]]]]p; subst. inv p.
    exists A'0. exists B'0.
    repeat split...
    apply: starSE...
    apply: starSE... }
Qed.

Lemma pred_ch_inv r A x :
  Ch r A ~>>* x ->
  exists A', A ~>>* A' /\ x = Ch r A'.
Proof with eauto.
  elim=>{x}.
  { exists A... }
  { move=>y z rd[A'[r1 e]]p; subst. inv p.
    exists A'0.
    repeat split...
    apply: starSE... }
Qed.

Lemma pred_fork_inv m n x :
  Fork m n ~>>* x ->
  exists m' n', m ~>>* m' /\ n ~>>* n' /\ x = Fork m' n'.
Proof with eauto.
  elim=>{x}.
  { exists m. exists n... }
  { move=>y z r[m'[n'[r1[r2 e]]]]p; subst. inv p.
    exists m'0. exists n'0.
    repeat split...
    apply: starSE...
    apply: starSE... }
Qed.

Lemma pred_recv_inv ch x :
  Recv ch ~>>* x ->
  exists ch', ch ~>>* ch' /\ x = Recv ch'.
Proof with eauto.
  elim=>{x}.
  { exists ch... }
  { move=>y z r[ch'[r1 e]]p; subst. inv p.
    exists ch'0.
    repeat split...
    apply: starSE... }
Qed.

Lemma pred_send_inv ch x :
  Send ch ~>>* x ->
  exists ch', ch ~>>* ch' /\ x = Send ch'.
Proof with eauto.
  elim=>{x}.
  { exists ch... }
  { move=>y z r[ch'[r1 e]]p; subst. inv p.
    exists ch'0.
    repeat split...
    apply: starSE... }
Qed.

Lemma pred_close_inv ch x :
  Close ch ~>>* x ->
  exists ch', ch ~>>* ch' /\ x = Close ch'.
Proof with eauto.
  elim=>{x}.
  { exists ch... }
  { move=>y z r[ch'[r1 e]]p; subst. inv p.
    exists ch'0.
    repeat split...
    apply: starSE... }
Qed.

Lemma pred_wait_inv ch x :
  Wait ch ~>>* x ->
  exists ch', ch ~>>* ch' /\ x = Wait ch'.
Proof with eauto.
  elim=>{x}.
  { exists ch... }
  { move=>y z r[ch'[r1 e]]p; subst. inv p.
    exists ch'0.
    repeat split...
    apply: starSE... }
Qed.

Lemma sort_inj s1 s2 :
  Sort s1 === Sort s2 -> s1 = s2.
Proof. move/church_rosser=>[x/pred_sort_inv->/pred_sort_inv[->//]]. Qed.

Lemma pi_inj A A' B B' s s' :
  Pi A B s === Pi A' B' s' -> A === A' /\ B === B' /\ s = s'.
Proof with eauto.
  move/church_rosser=>
   [x/pred_pi_inv[A1[B1[rA1[rB1->]]]]
     /pred_pi_inv[A2[B2[rA2[rB2[e1 e2 e3]]]]]]; subst.
  repeat split...
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma sigma_inj A A' B B' s s' :
  Sigma A B s === Sigma A' B' s' -> A === A' /\ B === B' /\ s = s'.
Proof with eauto.
  move/church_rosser=>
    [x/pred_sigma_inv[A1[B1[rA1[rB1->]]]]
      /pred_sigma_inv[A2[B2[rA2[rB2[e1 e2 e3]]]]]]; subst.
  repeat split...
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma act_inj r r' A A' B B' :
  Act r A B === Act r' A' B' -> A === A' /\ B === B' /\ r = r'.
Proof with eauto.
  move/church_rosser=>
    [x/pred_act_inv[A1[B1[rA1[rB1->]]]]
      /pred_act_inv[A2[B2[rA2[rB2[e1 e2 e3]]]]]]; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma ch_inj r r' A A' : Ch r A === Ch r' A' -> r = r' /\ A === A'.
Proof with eauto.
  move/church_rosser=>
    [x/pred_ch_inv[A1[r1->]]/pred_ch_inv[A2[r2[e1 e2]]]]; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv...
  apply: conv_sym. by apply: star_conv.
Qed.
