From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Export clc_soundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive head_sim : term -> term -> Prop :=
| head_sim_var x : head_sim (Var x) (Var x)
| head_sim_sort s : head_sim (Sort s) (Sort s)
| head_sim_pi A1 A2 B1 B2 s t :
  head_sim A1 A2 ->
  head_sim B1 B2 ->
  head_sim (Pi A1 B1 s t) (Pi A2 B2 s t)
| head_sim_lam A m s t : head_sim (Lam A m s t) (Lam A m s t)
| head_sim_app m n : head_sim (App m n) (App m n)
| head_sim_fix A m : head_sim (Fix A m) (Fix A m)
| head_sim_unit : head_sim (Unit) (Unit)
| head_sim_it : head_sim (It) (It)
| head_sim_either : head_sim (Either) (Either)
| head_sim_left : head_sim (Left) (Left)
| head_sim_right : head_sim (Right) (Right)
| head_sim_sigma A1 A2 B1 B2 s1 s2 r1 r2 t1 t2 :
  head_sim (Sigma A1 B1 s1 r1 t1) (Sigma A2 B2 s2 r2 t2)
| head_sim_pair m n t : head_sim (Pair m n t) (Pair m n t)
| head_sim_case A m n1 n2 : head_sim (Case A m n1 n2) (Case A m n1 n2)
| head_sim_letin1 A m n : head_sim (LetIn1 A m n) (LetIn1 A m n)
| head_sim_letin2 A m n : head_sim (LetIn2 A m n) (LetIn2 A m n)
| head_sim_main : head_sim (Main) (Main)
| head_sim_proto : head_sim (Proto) (Proto)
| head_sim_stop r : head_sim (Stop r) (Stop r)
| head_sim_act r A B s : head_sim (Act r A B s) (Act r A B s)
| head_sim_ch r A : head_sim (Ch r A) (Ch r A)
| head_sim_fork m n : head_sim (Fork m n) (Fork m n)
| head_sim_recv ch : head_sim (Recv ch) (Recv ch)
| head_sim_send ch : head_sim (Send ch) (Send ch)
| head_sim_close ch : head_sim (Close ch) (Close ch)
| head_sim_wait ch : head_sim (Wait ch) (Wait ch).

Inductive sim (m n : term) : Prop :=
| Sim x y : m === x -> head_sim x y -> y === n -> sim m n.

Lemma head_sim_refl m : head_sim m m.
Proof with eauto using head_sim. elim: m... Qed.
Hint Resolve head_sim_refl.

Lemma head_sim_subst m1 m2 σ : head_sim m1 m2 -> head_sim m1.[σ] m2.[σ].
Proof with eauto using head_sim.
  move=>hs. elim: hs σ=>{m1 m2}...
Qed.

Lemma sim_refl m : sim m m.
Proof with eauto. econstructor... Qed.
Hint Resolve sim_refl.

Lemma sim_transL x y z : sim x y -> y === z -> sim x z.
Proof with eauto.
  move=>sm eq. inv sm.
  econstructor...
  apply: conv_trans...
Qed.

Lemma sim_transR x y z : sim x y -> z === x -> sim z y.
Proof with eauto using head_sim.
  move=>sm eq. inv sm.
  econstructor.
  apply: conv_trans...
  apply: H0.
  apply: H1.
Qed.

Lemma sim_subst x y σ : sim x y -> sim x.[σ] y.[σ].
Proof with eauto.
  move=>sm. inv sm.
  econstructor.
  apply: conv_subst...
  apply: head_sim_subst...
  apply: conv_subst...
Qed.

Lemma sim_sort s t : sim (Sort s) (Sort t) -> s = t.
Proof with eauto.
  move e1:(Sort s)=>m.
  move e2:(Sort t)=>n sm.
  inv sm.
  elim: H0 s t H H1=>//{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>s r t/sort_inj->/sort_inj->//. }
  { move=>m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n1 n2 s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
Qed.

Lemma sim_pi_inj A1 A2 B1 B2 s1 s2 t1 t2 :
  sim (Pi A1 B1 s1 t1) (Pi A2 B2 s2 t2) ->
  sim A1 A2 /\ sim B1 B2 /\ s1 = s2 /\ t1 = t2.
Proof with eauto.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 t1 t2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>A1 A2 B1 B2 s t hA ihA hB ihB A0 A3 B0 B3 s1 s2 t1 t2
      /pi_inj[eqA1[eqB1[e1 e2]]]/pi_inj[eqA2[eqB2[e3 e4]]]; subst.
    repeat split.
    econstructor...
    econstructor... }
  { move=>m n A1 A2 B1 B2 s1 s2 t1 t2 eq1 eq2.
    have/pi_inj[eqA[eqB[->->]]]:=conv_trans _ eq1 eq2.
    repeat split.
    econstructor...
    econstructor... }
  { move=>A m A1 A2 B1 B2 s1 s2 t1 t2 eq1 eq2.
    have/pi_inj[eqA[eqB[->->]]]:=conv_trans _ eq1 eq2.
    repeat split.
    econstructor...
    econstructor... }
  { move=>A m n1 n2 A1 A2 B1 B2 s1 s2 t1 t2 eq1 eq2.
    have/pi_inj[eqA[eqB[->->]]]:=conv_trans _ eq1 eq2.
    repeat split.
    econstructor...
    econstructor... }
  { move=>A m n A1 A2 B1 B2 s1 s2 t1 t2 eq1 eq2.
    have/pi_inj[eqA[eqB[->->]]]:=conv_trans _ eq1 eq2.
    repeat split.
    econstructor...
    econstructor... }
  { move=>A m n A1 A2 B1 B2 s1 s2 t1 t2 eq1 eq2.
    have/pi_inj[eqA[eqB[->->]]]:=conv_trans _ eq1 eq2.
    repeat split.
    econstructor...
    econstructor... }
Qed.

Lemma sim_ch_inj A1 A2 r1 r2 :
  sim (Ch r1 A1) (Ch r2 A2) -> r1 = r2 /\ A1 === A2.
Proof with eauto.
  move=>sm. inv sm.
  elim: H0 A1 A2 r1 r2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>m n A1 A2 r1 r2 eq1 eq2.
    have/ch_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m A1 A2 r1 r2 eq1 eq2.
    have/ch_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n1 n2 A1 A2 r1 r2 eq1 eq2.
    have/ch_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n A1 A2 r1 r2 eq1 eq2.
    have/ch_inj//:=conv_trans _ eq1 eq2. } 
  { move=>A m n A1 A2 r1 r2 eq1 eq2.
    have/ch_inj//:=conv_trans _ eq1 eq2. } 
  { move=>r A A1 A2 r1 r2/ch_inj[-> eq1]/ch_inj[-> eq2].
    split...
    apply: conv_trans... }
Qed.

Lemma sim_act_inj A1 A2 B1 B2 s1 s2 r1 r2 :
  sim (Act r1 A1 B1 s1) (Act r2 A2 B2 s2) ->
    A1 === A2 /\ B1 === B2 /\ s1 = s2 /\ r1 = r2 .
Proof with eauto.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 r1 r2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>m n A1 A2 B1 B2 s1 s2 r1 r2 eq1 eq2.
    have/act_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m A1 A2 B1 B2 s1 s2 r1 r2 eq1 eq2.
    have/act_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n1 n2 A1 A2 B1 B2 s1 s2 r1 r2 eq1 eq2.
    have/act_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n A1 A2 B1 B2 s1 s2 r1 r2 eq1 eq2.
    have/act_inj//:=conv_trans _ eq1 eq2. }
  { move=>A m n A1 A2 B1 B2 s1 s2 r1 r2 eq1 eq2.
    have/act_inj//:=conv_trans _ eq1 eq2. }
  { move=>r A B s A1 A2 B1 B2 s1 s2 r1 r2
      /act_inj[eq1[eq2[e1 e2]]]/act_inj[eq3[eq4[e3 e4]]]; subst.
    repeat split...
    apply: conv_trans...
    apply: conv_trans... }
Qed.

Lemma clc_sort_uniq Γ s A :
  Γ ⊢ Sort s : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Sort s)=>n ty. elim: ty s e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB t e; subst.
  have eq':=ihm _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_pi_uniq Γ A B s t C :
  Γ ⊢ Pi A B s t : C -> sim (Sort t) C.
Proof with eauto using head_sim.
  move e:(Pi A B s t)=>n ty. elim: ty A B s t e=>//{Γ n C}.
  move=>Γ A B s r t k tyA ihA tyB ihB A0 B0 s0 t0[e1 e2 e3->]//.
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 t e; subst.
  have eq':=ihm _ _ _ _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_has_subset Γ Γ1 Γ2 G1 G2 A B x s t :
  has Γ1 x s A -> has Γ2 x t B -> Γ1 ∘ G1 => Γ -> Γ2 ∘ G2 => Γ -> A = B /\ s = t.
Proof with eauto.
  move=>hs. elim: hs Γ Γ2 G1 G2 B t=>{Γ1 x s A}.
  move=>Γ A s k Γ0 Γ2 G1 G2 B t hs mrg1 mrg2.
  { inv mrg1; inv mrg2; inv hs... }
  move=>Γ A B x s hs1 ih Γ0 Γ2 G1 G2 B0 t hs2 mrg1 mrg2.
  { inv mrg1. inv mrg2. inv hs2.
    have[->->//]:=ih _ _ _ _ _ _ H6 H3 H2. }
  move=>Γ A x s hs1 ih Γ0 Γ2 G1 G2 B t hs2 mrg1 mrg2.
  { inv mrg1. inv mrg2; inv hs2.
    have[->->//]:=ih _ _ _ _ _ _ H2 H0 H3.
    inv mrg2. inv hs2.
    have[->->//]:=ih _ _ _ _ _ _ H2 H0 H3. }
Qed.
    
Lemma clc_has_uniq Γ A B x s t : has Γ x s A -> has Γ x t B -> A = B.
Proof with eauto.
  move=>hs. elim: hs B t=>{Γ x s A}.
  move=>Γ A s k B t hs. inv hs...
  move=>Γ A B x s hs1 ih B0 t hs2.
  { inv hs2. rewrite (ih _ _ H4)... }
  move=>Γ A x s hs1 ih B t hs2.
  { inv hs2. rewrite (ih _ _ H1)... }
Qed.

Lemma clc_lam_uniq Γ A B C m s t :
  Γ ⊢ Lam A m s t : C -> (forall C, A :{s} Γ ⊢ m : C -> sim B C) -> sim (Pi A B s t) C.
Proof with eauto.
  move e:(Lam A m s t)=>n ty. elim: ty A B m s t e=>//{Γ n C}.
  move=>Γ A B m s t k tyP ihP tym ihm A0 B0 m0 s0 t0[e1 e2 e3 e4]h; subst.
  { have eq':=h _ tym. inv eq'.
    econstructor.
    apply: conv_pi.
    eauto.
    apply: H.
    constructor.
    eauto.
    apply: H0.
    apply: conv_pi... }
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 t e h; subst.
  { have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma clc_app_uniq Γ A B C m n s t :
  Γ ⊢ App m n : C ->
  (forall C Γ1 Γ2, Γ1 ∘ Γ2 => Γ -> Γ1 ⊢ m : C -> sim (Pi A B s t) C) -> sim B.[n/] C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s t e=>//{Γ x C}.
  move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn
     A0 B0 m0 n0 s0 t0[e1 e2]h; subst.
  { have/sim_pi_inj[_[eq' _]]:=h _ _ _ mrg tym.
    apply: sim_subst... }
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 t e h; subst.
  { have eq':=ihm _ _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma clc_fix_uniq Γ A B m : Γ ⊢ Fix A m : B -> sim A B.
Proof with eauto.
  move e:(Fix A m)=>n ty. elim: ty A m e=>//{Γ B n}.
  move=>Γ A m k tyA ihA tym ihm A0 m0[e1 e2]; subst...
  move=>Γ A B m s eq tym ihm tyB ihB A0 m0 e; subst.
  { have eq':=ihm _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma clc_unit_uniq Γ A : Γ ⊢ Unit : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Unit)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma clc_it_uniq Γ A : Γ ⊢ It : A -> sim Unit A.
Proof with eauto.
  move e:(It)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma clc_either_uniq Γ A : Γ ⊢ Either : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Either)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma clc_left_uniq Γ A : Γ ⊢ Left : A -> sim Either A.
Proof with eauto.
  move e:(Left)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma clc_right_uniq Γ A : Γ ⊢ Right : A -> sim Either A.
Proof with eauto.
  move e:(Right)=>m ty. elim: ty e=>//{Γ m A}.
  move=>Γ A B m s eq tym ihm tyB ihB e; subst.
  { have eq':=ihm erefl.
    apply: sim_transL... }
Qed.

Lemma clc_sigma_uniq Γ A B C s r t :
  Γ ⊢ Sigma A B s r t : C -> sim (Sort t) C.
Proof with eauto.
  move e:(Sigma A B s r t)=>m ty. elim: ty A B s r t e=>//{Γ m C}.
  move=>Γ A B s r t leq k tyA ihA tyB ihB A0 B0 s0 r0 t0[e1 e2 e3 e4 e5]; subst...
  move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 r t e; subst.
  { have eq':=ihm _ _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma clc_pair_uniq Γ A B C m n s r t :
  Γ ⊢ Pair m n t : C ->
  (forall Γ1 Γ2 G1 G2 X Y,
      Γ1 ⊢ m : X -> Γ1 ∘ G1 => Γ ->
      Γ2 ⊢ n : Y -> G2 ∘ Γ2 => Γ -> sim A X /\ sim B.[m/] Y) -> sim (Sigma A B s r t) C.
Proof with eauto.
  move e:(Pair m n t)=>x ty. elim: ty A B m n t s r e=>//{Γ C x}.
  { move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg tyS _ tym _ tyn _ A0 B0 m0 n0
      t0 s0 r0[e1 e2 e3]h; subst.
    econstructor. eauto.
    constructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB _ A0 B0 m0 n t s0 r e h; subst.
    have eq':=ihm _ _ _ _ _ s0 r erefl h.
    apply: sim_transL... }
Qed.

Lemma clc_case_uniq Γ m n1 n2 A B :
  Γ ⊢ Case A m n1 n2 : B -> sim A.[m/] B.
Proof with eauto.
  move e:(Case A m n1 n2)=>x ty. elim: ty A m n1 n2 e=>//{Γ B x}.
  { move=>Γ1 Γ2 Γ m n1 n2 A s t k mrg tym _ tyA _ tyn1 _ tyn2 _
      A0 m0 n0 n3[e1 e2 e3 e4]; subst.
    apply: sim_refl. }
  { move=>Γ A B m s eq tym ihm tyB _ A0 m0 n1 n2 e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma clc_letin1_uniq Γ m n A B :
  Γ ⊢ LetIn1 A m n : B -> sim A.[m/] B.
Proof with eauto.
  move e:(LetIn1 A m n)=>x ty. elim: ty A m n e=>//{Γ B x}.
  { move=>Γ1 Γ2 Γ m n A s t k mrg tym _ tyA _ tyn _
      A0 m0 n0[e1 e2 e3]; subst.
    apply: sim_refl. }
  { move=>Γ A B m s k tym ihm tyB _ A0 m0 n e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.
    
Lemma clc_letin2_uniq Γ m n A B :
  Γ ⊢ LetIn2 A m n : B -> sim A.[m/] B.
Proof with eauto.
  move e:(LetIn2 A m n)=>x ty. elim: ty A m n e=>//{Γ B x}.
  { move=>Γ1 Γ2 Γ A B C m n s r t k x leq key mrg tym _ tyC _ tyn _
      A0 m0 n0[e1 e2 e3]; subst.
    apply: sim_refl. }
  { move=>Γ A B m s k tym ihm tyB _ A0 m0 n e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma clc_main_uniq Γ B :
  Γ ⊢ Main : B -> sim (Sort L) B.
Proof with eauto.
  move e:(Main)=>x ty. elim: ty e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ e; subst.
  have eq':=ih erefl.
  apply: sim_transL...
Qed.

Lemma clc_proto_uniq Γ B :
  Γ ⊢ Proto : B -> sim (Sort U) B.
Proof with eauto.
  move e:(Proto)=>x ty. elim: ty e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ e; subst.
  have eq':=ih erefl.
  apply: sim_transL...
Qed.

Lemma clc_stop_uniq Γ B r :
  Γ ⊢ Stop r : B -> sim (Proto) B.
Proof with eauto.  
  move e:(Stop r)=>x ty. elim: ty r e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ r e; subst.
  have eq':=ih _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_act_uniq Γ A B C s r :
  Γ ⊢ Act r A B s : C -> sim (Proto) C.
Proof with eauto.  
  move e:(Act r A B s)=>x ty. elim: ty A B s r e=>//{Γ x C}.
  move=>Γ A B m s eq tym ihm tyB _ A0 B0 s0 r e; subst.
  have eq':=ihm _ _ _ _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_ch_uniq Γ A B r :
  Γ ⊢ Ch r A : B -> sim (Sort L) B.
Proof with eauto.
  move e:(Ch r A)=>x ty. elim: ty r A e=>//{Γ x B}.
  move=>Γ A B m s eq tym ihm tyB _ r A0 e; subst.
  have eq':=ihm _ _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_fork_uniq Γ m n A C r :
  Γ ⊢ Fork m n : C -> sim (Sigma (Ch (~~r) A) Main L L L) C.
Proof with eauto.
  move e:(Fork m n)=>x ty. elim: ty A m n r e=>//{Γ x C}.
  { move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tym _ tyn _
      A0 B0 m0 r[e1 e2]; subst.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB _ A0 B0 m0 r e; subst.
    have eq':=ihm _ _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma clc_recv_uniq Γ m A B C s r :
  Γ ⊢ Recv m : C -> sim (Sigma A (Ch r B) s L L) C.
Proof with eauto.
  move e:(Recv m)=>x ty. elim: ty A B m s r e=>//{Γ x C}.
  { move=>*.
    econstructor. eauto.
    econstructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB _ A0 B0 m0 s0 r e; subst.
    have eq':=ihm A0 B0 _ s0 r erefl.
    apply: sim_transL... }
Qed.

Lemma clc_send_uniq Γ m A B C s r1 r2 :
  Γ ⊢ Send m : C ->
  (forall C, Γ ⊢ m : C -> sim (Ch r1 (Act r2 A B s)) C) ->
  sim (Pi A (Ch r1 B) s L) C.
Proof with eauto.
  move e:(Send m)=>x ty. elim: ty A B m s r1 r2 e=>//{Γ x C}.
  { move=>Γ r1 r2 A B m s xor tym _ A0 B0 m0 s0 r0 r3[e]h; subst.
    have/sim_ch_inj[->/act_inj[eq1[eq2[->_]]]]:=h _ tym.
    econstructor.
    apply: conv_pi.
    apply: eq1.
    apply: conv_ch.
    apply: eq2.
    apply: head_sim_refl.
    eauto. }
  { move=>Γ A B m s eq tym ihm tyB _ A0 B0 m0 s0 r1 r2 e h; subst.
    have eq':=ihm _ _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma clc_wait_uniq Γ m B : Γ ⊢ Wait m : B -> sim Unit B.
Proof with eauto.
  move e:(Wait m)=>x ty. elim: ty m e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ m0 e; subst.
  have eq':=ih _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_close_uniq Γ m B : Γ ⊢ Close m : B -> sim Unit B.
Proof with eauto.
  move e:(Close m)=>x ty. elim: ty m e=>//{Γ x B}.
  move=>Γ A B m s eq tym ih tyB _ m0 e; subst.
  have eq':=ih _ erefl.
  apply: sim_transL...
Qed.

Lemma clc_uniq Γ1 Γ2 G1 G2 Γ m A B :
  Γ1 ⊢ m : A -> Γ2 ⊢ m : B -> Γ1 ∘ G1 => Γ -> Γ2 ∘ G2 => Γ -> sim A B.
Proof with eauto.
  move=>ty. elim: ty Γ2 G1 G2 Γ B=>{Γ1 m A}.
  { move=>Γ s k Γ2 G1 G2 Γ0 B tyS mrg1 mrg2.
    apply: clc_sort_uniq... }
  { move=>Γ A B s r t k tyA ihA tyB ihB Γ1 G1 G2 Γ0 B0 tyP mrg3 mrg4.
    apply: clc_pi_uniq... }
  { move=>Γ x A s hs Γ2 G1 G2 Γ0 B tyV mrg1 mrg2.
    have[X[v[hsx eq]]]:=var_inv tyV.
    have[-> _//]:=clc_has_subset hs hsx mrg1 mrg2.
    econstructor... }
  { move=>Γ A B m s t k tyP ihP tym ihm Γ2 G1 G2 Γ0 B0 tyL mrg1 mrg2.
    apply:clc_lam_uniq...
    move=>C tym'.
    destruct s.
    have{}mrg1: A :U Γ ∘ A :U G1 => A :U Γ0 by constructor.
    have{}mrg2: A :U Γ2 ∘ A :U G2 => A :U Γ0 by constructor.
    apply: ihm...
    have{}mrg1: A :L Γ ∘ _: G1 => A :L Γ0 by constructor.
    have{}mrg2: A :L Γ2 ∘ _: G2 => A :L Γ0 by constructor.
    apply: ihm... }
  { move=>Γ1 Γ2 Γ A B m n s t k mrg tym ihm tyn ihn Γ0 G1 G2 Γ3 B0 tyA mrg1 mrg2.
    have[D[mrg3 mrg4]]:=merge_splitR mrg1 mrg.
    apply: clc_app_uniq...
    move=>C Γ4 Γ5 mrg5 tym'.
    have[Dx[mrg6 mrg7]]:=merge_splitR mrg2 mrg5.
    apply: ihm.
    apply: tym'.
    apply: mrg4.
    apply: mrg7. }
  { move=>Γ A m k tyA ihA tym ihm Γ2 G1 G2 Γ0 B tyF mrg1 mrg2.
    apply: clc_fix_uniq... }
  { move=>Γ k Γ1 G1 G2 Γ0 B tyU mrg1 mrg2.
    apply: clc_unit_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyI mrg1 mrg2.
    apply: clc_it_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyE mrg1 mrg2.
    apply: clc_either_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyL mrg1 mrg2.
    apply: clc_left_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyR mrg1 mrg2.
    apply: clc_right_uniq... }
  { move=>Γ A B s r t leq k tyA ihA tyB ihB Γ2 G1 G2 Γ0 B0 tyS mrg1 mrg2.
    apply: clc_sigma_uniq... }
  { move=>Γ1 Γ2 Γ A B m n s r t k1 k2 mrg tyS ihS tym ihm tyn ihn Γ0 G1 G2 Γ3 B0 tyP mrg1 mrg2.
    apply: clc_pair_uniq...
    move=>Γ4 Γ5 G0 G3 X Y tyx mrgx tyy mrgy. split.
    have[D1[mrg3 mrg4]]:=merge_splitR mrg1 mrg.
    have[D2[mrg5 mrg6]]:=merge_splitR mrg2 mrgx.
    apply: ihm. exact: tyx. exact: mrg4. exact: mrg6.
    have[D1[mrg3 mrg4]]:=merge_splitR mrg1 (merge_sym mrg).
    have[D2[mrg5 mrg6]]:=merge_splitR mrg2 (merge_sym mrgy).
    apply: ihn. exact: tyy. exact: mrg4. exact: mrg6. }
  { move=>Γ1 Γ2 Γ m n1 n2 A s t k mrg tym ihm tyA ihA tyn1 ihn1 tyn2 ihn2
      Γ0 G1 G2 Γ3 B tyC mrg1 mrg2.
    apply: clc_case_uniq... }
  { move=>Γ1 Γ2 Γ m n A s t k mrg tym ihm tyA ihA tyn ihn
      Γ0 G1 G2 Γ3 B tyL mrg1 mrg2.
    apply: clc_letin1_uniq... }
  { move=>Γ1 Γ2 Γ A B C m n s r t k x leq key mrg tym _ tyC _ tyn _
      Γ0 G1 G2 Γ3 B0 tyL mrg1 mrg2.
    apply: clc_letin2_uniq... }
  { move=>Γ k Γ1 G1 G2 Γ0 B tyM mrg1 mrg2.
    apply: clc_main_uniq... }
  { move=>Γ k Γ2 G1 G2 Γ0 B tyP mrg1 mrg2.
    apply: clc_proto_uniq... }
  { move=>Γ r k Γ2 G1 G2 Γ0 B tyS mrg1 mrg2.
    apply: clc_stop_uniq... }
  { move=>Γ r A B s k tyA ihA tyB ihB Γ2 G1 G2 Γ0 B0 ty mrg1 mrg2.
    apply: clc_act_uniq... }
  { move=>Γ r A k tyA ihA Γ2 G1 G2 Γ0 B tyC mrg1 mrg2.
    apply: clc_ch_uniq... }
  { move=>Γ1 Γ2 r1 r2 Γ m n A B t mrg d tym ihm tyn ihn
      Γ0 G1 G2 Γ3 B0 tyF mrg1 mrg2; subst.
    apply: clc_fork_uniq... }
  { move=>Γ r1 r2 A B m s xor tym ihm Γ2 G1 G2 Γ0 B0 ty mrg1 mrg2.
    apply: clc_recv_uniq... }
  { move=>Γ r1 r2 A B m s xor tym ihm Γ2 G1 G2 Γ0 B0 ty mrg1 mrg2.
    apply: clc_send_uniq... }
  { move=>Γ r1 r2 m xor tym ihm Γ2 G1 G2 Γ0 B ty mrg1 mrg2.
    apply: clc_wait_uniq... }
  { move=>Γ r1 r2 m xor tym ihm Γ2 G1 G2 Γ0 B ty mrg1 mrg2.
    apply: clc_close_uniq... }
  { move=>Γ A B m s eq tym ihm tyB _ Γ2 G1 G2 Γ0 B0 ty mrg1 mrg2.
    have eq':=ihm _ _ _ _ _ ty mrg1 mrg2.
    apply: sim_transR...
    apply: conv_sym... }
Qed.

Theorem unicity Γ m s t :
  Γ ⊢ m : Sort s -> Γ ⊢ m : Sort t -> s = t.
Proof with eauto.
  move=>ty1 ty2.
  apply: sim_sort.
  apply: clc_uniq.
  apply: ty1.
  apply: ty2.
  apply: merge_reR.
  apply: merge_reR.
Qed.
  
