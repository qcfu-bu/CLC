From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Import AutosubstSsr ARS
  clc_context clc_ast clc_confluence clc_subtype clc_typing
  clc_weakening clc_substitution clc_inversion clc_arity_spine
  clc_validity clc_typing_spine clc_respine clc_iota_lemma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma arity_step s A A' : arity s A -> A ~> A' -> arity s A'.
Proof.
  move=>ar. elim: ar A'=>{A}.
  move=> l A' st. inv st.
  move=> A0 B a ih A' st. inv st.
  constructor; eauto.
  constructor; eauto.
Qed.

Inductive n_beta k (σ : var -> term) x :=
| N_beta :
  k < x.+1 ->
  (forall i, i < k -> σ i = (Var i)) ->
  noccurs x (σ k) ->
  (forall i, k < i -> (σ i).[ren (+1)] = Var i) ->
  n_beta k σ x.

Lemma noccurs_n_beta x m : noccurs x m -> n_beta 0 (m .: ids) x.
Proof.
  move=>no. constructor; eauto.
  move=>[|i] h; inv h.
  move=>[|i] h; inv h.
  asimpl; eauto.
Qed.

Lemma n_beta_up k x σ : n_beta k σ x -> n_beta k.+1 (up σ) x.+1.
Proof.
  move=>[lt h1 h2 h3].
  constructor; eauto.
  move=>[|i h]; eauto; asimpl.
  have/h1->//: i < k by eauto.
  asimpl. apply: noccurs_up; eauto.
  move=>[|i] h; asimpl. inv h.
  replace (σ i).[ren (+2)] with (σ i).[ren (+1)].[ren (+1)] by autosubst.
  have/h3->//: k < i by eauto.
Qed.

Lemma lt_false x y : x < y -> y < x.+1 -> False.
Proof.
  elim: x y.
  move=>[|y] h1 h2; inv h1. inv h2.
  move=>n ih [|y] h1 h2. inv h1.
  apply: ih; eauto.
Qed.

Lemma noccurs_beta k x m σ : noccurs x.+1 m -> n_beta k σ x -> noccurs x m.[σ].
Proof with eauto using n_beta, n_beta_up.
  move e:(x.+1)=>i no. move: i m no σ k x e.
  apply: noccurs_ind_nested=>//=.
  all: try solve[intros; subst; eauto using noccurs, n_beta, n_beta_up ].
  move=>x y neq σ k x0 e [leq h1 no h3]; subst.
  { have[h|h|h]:=ltngtP k y.
    have{}h:=h3 _ h.
    destruct (σ y)=>//. inv h.
    constructor...
    rewrite h1...
    constructor.
    move=>e; subst.
    apply: lt_false...
    subst... }
  move=>x A Cs s nA ih nCs ihCs σ k x0 e nb; subst.
  { constructor...
    elim: ihCs. constructor.
    move=>C Cs' hd tl ihc.
    constructor... }
  move=>x m Q Fs nm ihm nQ ihQ nFs ihFs σ k x0 e nb; subst.
  { constructor...
    elim: ihFs. constructor.
    move=>C Cs' hd tl ihc.
    constructor... }
Qed.

Lemma noccurs_spine' x h1 h2 ms :
  noccurs x (spine' h1 ms) -> noccurs x h2 -> noccurs x (spine' h2 ms).
Proof.
  move e:(spine' h1 ms)=> n no. move: x n no h1 h2 ms e.
  apply: noccurs_ind_nested; move=>*;
  match goal with
  | [ H : spine' _ ?ms = _ |- _ ] =>
    destruct ms; simpl; simpl in H; inv H; eauto
  end.
  constructor; eauto.
Qed.

Lemma noccurs_spine x h1 h2 ms :
  noccurs x (spine h1 ms) -> noccurs x h2 -> noccurs x (spine h2 ms).
Proof.
  rewrite! spine_spine'_rev=> noSp no.
  apply: noccurs_spine'; eauto.
Qed.

Lemma noccurs_step x m n : noccurs x m -> m ~> n -> noccurs x n.
Proof with eauto using noccurs, noccurs_beta, noccurs_n_beta.
  move=> no. move: x m no n.
  apply: noccurs_ind_nested;
  try solve [intros;
             match goal with
             | [ H : step _ _ |- _ ] =>
                 inv H; eauto using noccurs
             end].
  move=>x m n nm ihm nn ihn n0 st. inv st... inv nm...
  move=>x A Cs s nA ihA nCs ihCs n st.
  { inv st...
    constructor...
    elim: H3 ihCs nCs.
    move=>m m' ls st h1 h2. inv h1. inv h2. constructor...
    move=>m ls ls' h1 h2 h3 h4. inv h3. inv h4. constructor... }
  move=>x m Q Fs nm ihm nQ ihQ nFs ihFs n st.
  { inv st...
    constructor...
    elim: H3 ihFs nFs.
    move=>m0 m' ls st h1 h2. inv h1. inv h2. constructor...
    move=>m0 ls ls' h1 h2 h3 h4. inv h3. inv h4. constructor...
    apply: noccurs_spine...
    elim: H3 nFs.
    move=>m ls nFs. inv nFs...
    move=>n m m' ls ig ih nFs. inv nFs... }
  move=>x A m nA ihA nm ihm n st. inv st...
Qed.

Lemma head_spine'_step h h' ms : h ~> h' -> spine' h ms ~> spine' h' ms.
Proof.
  elim: ms h h'; eauto.
  move=> h ms ih h1 h2 st; simpl.
  constructor; eauto.
Qed.

Lemma head_spine'_conv h h' ms : h === h' -> spine' h ms === spine' h' ms.
Proof.
  elim: ms h h'; eauto.
  move=> h ms ih h1 h2 e; simpl.
  apply: conv_app; eauto.
Qed.

Lemma head_spine_step h h' ms : h ~> h' -> spine h ms ~> spine h' ms.
Proof.
  rewrite! spine_spine'_rev=>st.
  apply: head_spine'_step; eauto.
Qed.

Lemma head_spine_conv h h' ms : h === h' -> spine h ms === spine h' ms.
Proof.
  rewrite! spine_spine'_rev=>st.
  apply: head_spine'_conv; eauto.
Qed.

Lemma var_spine'_step x ms C :
  spine' (Var x) ms ~> C -> All1 (noccurs x) ms ->
  exists ms', C = spine' (Var x) ms' /\ All1 (noccurs x) ms'.
Proof.
  elim: ms x C=>//=.
  move=> x C st. inv st.
  move=> a l ih x C st no.
  inv no. inv st.
  destruct l; inv H0.
  have[ms'[e no]]:=ih x m' H4 H2; subst.
  exists (a :: ms')=>//=. repeat constructor; eauto.
  exists (n' :: l)=>//=. repeat constructor; eauto.
  apply: noccurs_step; eauto.
Qed.

Lemma noccurs_All1_cat x ms ns :
  All1 (noccurs x) ms -> All1 (noccurs x) ns -> All1 (noccurs x) (ms ++ ns).
Proof with eauto using All1. move=>no. elim: no ns... Qed.

Lemma noccurs_All1_rev x ms : All1 (noccurs x) ms -> All1 (noccurs x) (rev ms).
Proof with eauto using All1.
  elim: ms=>//=.
  move=>m ms ih nms. inv nms.
  have{H2}ih:=ih H2.
  replace (m :: ms) with ([:: m] ++ ms) by eauto.
  rewrite rev_cat.
  apply: noccurs_All1_cat...
Qed.

Lemma var_spine_step x ms C :
  spine (Var x) ms ~> C -> All1 (noccurs x) ms ->
  exists2 ms', C = spine (Var x) ms' & All1 (noccurs x) ms'.
Proof.
  rewrite! spine_spine'_rev.
  move=>st/noccurs_All1_rev no.
  have[ms' [h1 h2]]:=var_spine'_step st no.
  exists (rev ms').
  rewrite spine_spine'_rev. rewrite revK; eauto.
  apply: noccurs_All1_rev; eauto.
Qed.

Lemma pos_step x A B : pos x A -> A ~> B -> pos x B.
Proof.
  move=> p. elim: p B=>{A x}.
  move=> x ms no B st.
  have[ms'[e no']]:=var_spine_step st no; subst.
  constructor; eauto.
  move=>x A B s r t n p ih B' st. inv st.
  constructor; eauto.
  apply: noccurs_step; eauto.
  constructor; eauto.
Qed.

Lemma constr_step x s C C' : constr x s C -> C ~> C' -> constr x s C'.
Proof.
  move=>c. elim: c C'=>{C x s}.
  move=>x s ms nms C' st.
  { have[ms' e nms']:=var_spine_step st nms; subst.
    constructor; eauto. }
  move=>s t x A B leq pA nB cB ih C' st. inv st.
  { apply: constr_pos; eauto.
    apply: pos_step; eauto. }
  { apply: constr_pos; eauto.
    apply: noccurs_step; eauto. }
  move=>s t x A B leq nB cB ih C' st. inv st.
  { apply: constr_pi; eauto.
    apply: noccurs_step; eauto. }
  { apply: constr_pi; eauto. }
Qed.

Lemma iget_step i Cs Cs' C :
  iget i Cs C -> One2 step Cs Cs' ->
  exists2 C', C === C' & iget i Cs' C'.
Proof.
  move=>ig h. elim: h i ig=>{Cs Cs'}.
  move=>m m' ls st i ig. inv ig.
  { exists m'; repeat constructor; eauto. apply: conv1; eauto. }
  { exists C; repeat constructor; eauto. }
  move=>m ls ls' st ih i ig. inv ig.
  { exists C; repeat constructor; eauto. }
  { have[C' cC ig]:=ih _ H3.
    exists C'; repeat constructor; eauto. }
Qed.

Lemma respine0_step Q Q' C : Q ~> Q' -> respine0 Q C ~> respine0 Q' C.
Proof with eauto using step. elim: C Q Q'... Qed.

Lemma respine_step k s Q Q' c C :
  Q ~> Q' ->
  (respine k s Q c C).1 = (respine k s Q' c C).1 /\
  (respine k s Q c C).2 ~> (respine k s Q' c C).2.
Proof with eauto using step, respine0_step.
  elim: C k s Q Q' c.
  move=>x [|] s Q Q' c st//=...
  move=>s l [|] s0 Q Q' c st//=...
  move=>A ihA B ihB s r t [|] s0 Q Q' c st//=.
  { pose proof (step_subst (ren (+1)) st) as st'.
    pose proof (ihB U s0 _ _ (App c.[ren (+1)] (Var 0)) st') as [h1 h2].
    remember (respine U s0 Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) B) as p1.
    remember (respine U s0 Q'.[ren (+1)] (App c.[ren (+1)] (Var 0)) B) as p2.
    destruct p1.
    destruct p2.
    simpl.
    split; eauto.
    simpl in h1; subst.
    simpl in h2.
    constructor; eauto. }
  { pose proof (step_subst (ren (+1)) st) as st'.
    pose proof (ihB L s0 _ _ (App c.[ren (+1)] (Var 0)) st') as [h1 h2].
    remember (respine L s0 Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) B) as p1.
    remember (respine L s0 Q'.[ren (+1)] (App c.[ren (+1)] (Var 0)) B) as p2.
    destruct p1.
    destruct p2.
    simpl.
    split; eauto.
    simpl in h1; subst.
    simpl in h2.
    constructor; eauto. }
  move=>A ihA m ihm s t [|] s0 Q Q' c st//=...
  move=>m ihm n ihn [|] s Q Q' c st//=...
  move=>A ihA Cs s [|] s0 Q Q' c st//=...
  move=>i m ihm [|] s Q Q' c st//=...
  move=>m ihm Q ihQ Fs [|] s Q0 Q' c st//=...
  move=>A ihA m ihm [|] s Q Q' c st//=...
Qed.

Lemma mkcase_step k s I Q Q' c C :
  Q ~> Q' ->
  (mkcase k s I Q c C).1 = (mkcase k s I Q' c C).1 /\
  (mkcase k s I Q c C).2 ~> (mkcase k s I Q' c C).2.
Proof.
  move=>st. unfold mkcase.
  apply: respine_step; eauto.
Qed.

Inductive sub_list : nat -> list term -> list term -> Prop :=
| sub_list_O xs : sub_list 0 xs xs
| sub_list_S x xs ys n :
  sub_list n xs ys -> sub_list n.+1 (x :: xs) ys.

Lemma sub_list_iget i XS x xs :
  sub_list i XS (x :: xs) -> iget i XS x.
Proof.
  move e:(x :: xs)=> ys sb.
  elim: sb x xs e=>{i XS ys}.
  move=>xs x xs0 e; subst. constructor.
  move=>x xs ys n sbl ih x0 xs0 e; subst.
  constructor; eauto.
Qed.

Lemma sub_list_ok i XS x xs :
  sub_list i XS (x :: xs) -> sub_list i.+1 XS xs.
Proof.
  move e:(x :: xs)=> ys sb.
  elim: sb x xs e=>{i XS ys}.
  move=>xs s xs0 e; subst. repeat constructor.
  move=>x xs ys n sbl ih x0 xs0 e; subst.
  constructor; eauto.
Qed.

Lemma All2i_strengthen (P : nat -> term -> term -> Prop) Cs Fs Xs n :
  All2i (fun i F C => P i F C) n Fs Xs ->
  sub_list n Cs Xs ->
  All2i (fun i F C => iget i Cs C /\ P i F C) n Fs Xs.
Proof.
  move=> a2i. elim: a2i Cs=>{Fs Xs n}.
  move=>i Cs sbl. constructor.
  move=>i m m' ls ls' pm hd ih Cs sbl.
  constructor.
  move/sub_list_iget in sbl=>//.
  apply: ih. apply: sub_list_ok; eauto.
Qed.

Lemma All2i_mkcase_stepQ Γ A Q Q' Fs Cs Xs n k s s' l :
  let I := Ind A Cs s in
  s ≤ k ->
  Q ~> Q' ->
  arity s A ->
  [Γ] ⊢ I : A : U ->
  [Γ] ⊢ Q' : rearity k s' I A : U ->
  sub_list n Cs Xs ->
  All2i (fun i F C =>
    constr 0 s C /\
    let T := mkcase k s' I Q (Constr i I) C in
    Γ ⊢ F : T.2 : T.1) n Fs Xs ->
  All1 (fun C => A :U [Γ] ⊢ C : s @ l : U) Xs ->
  All2i (fun i F C =>
    constr 0 s C /\
    let T := mkcase k s' I Q' (Constr i I) C in
    Γ ⊢ F : T.2 : T.1) n Fs Xs.
Proof.
  move=>I leq st ar tyI tyQ sbl a2i.
  have{sbl}a2i:=All2i_strengthen a2i sbl. elim: a2i=>{Fs Xs}.
  constructor.
  move=>i F C Fs Cs'[ig[cm tym]] hd ih tl. inv tl.
  constructor; eauto.
  split; eauto.
  have h1 : (I .: ids) 0 = Ind A Cs s by eauto.
  have h2 : [Γ] ⊢ C.[I/] : (s @ l).[I/] : U.
  { apply: substitution.
    apply: H1.
    apply: (re_pure Γ).
    apply: merge_re_id.
    eauto. }
  pose proof (respine_step k s' (Constr i I) C.[I/] st) as [h3 h4].
  have{}h4 :
    (respine k s' Q (Constr i I) C.[I/]).2 <:
    (respine k s' Q' (Constr i I) C.[I/]).2.
  { apply: conv_sub.
    apply: conv1; eauto. }
  have h5 : [Γ] ⊢ Constr i I : C.[I/] : s.
  { apply: clc_constr; eauto.
    apply: re_pure. }
  destruct k.
  { inv leq.
    have//=[l0 ty]:=constr_respineU cm ar h1 tyI tyQ h2 h5.
    unfold mkcase.
    unfold mkcase in tym.
    apply: clc_conv.
    apply: h4.
    rewrite<-h3.
    apply: tym.
    eauto. }
  { have//=[l0 ty]:=constr_respineL (Constr i I) cm ar h1 tyI tyQ h2.
    unfold mkcase.
    unfold mkcase in tym.
    apply: clc_conv.
    apply: h4.
    rewrite<-h3.
    apply: tym.
    eauto. }
Qed.

Lemma All2i_One2_stepF Γ A Q Fs Fs' Cs Cs' n k s s' :
  let I := Ind A Cs' s in
  ok Γ ->
  One2 step Fs Fs' ->
  All2i (fun i F C =>
    constr 0 s C /\
    let T := mkcase k s' I Q (Constr i I) C in
    Γ ⊢ F : T.2 : T.1) n Fs Cs ->
  All2i (fun i F C =>
    constr 0 s C /\ (ok Γ -> forall F',
    F ~> F' ->
    let T := mkcase k s' I Q (Constr i I) C in
    Γ ⊢ F' : T.2 : T.1)) n Fs Cs ->
  All2i (fun i F C =>
    constr 0 s C /\
    let T := mkcase k s' I Q (Constr i I) C in
    Γ ⊢ F : T.2 : T.1) n Fs' Cs.
Proof.
  move=>I wf oFs. elim: oFs Cs n=>{Fs Fs'}.
  move=>F F' Fs' st Cs n hd tl. inv hd. inv tl.
  { constructor; eauto.
    inv H5. split; eauto. }
  move=>F Fs Fs' oFs ih Cs n hd tl. inv hd. inv tl.
  { constructor; eauto. }
Qed.

Theorem subject_step Γ m n A s :
  ok Γ -> Γ ⊢ m : A : s -> m ~> n -> Γ ⊢ n : A : s.
Proof with eauto using clc_type, step, ok, merge_re_id.
  move=>wf tp.
  move: Γ m A s tp n wf. apply: clc_type_ind_nested.
  move=>Γ s l k n o st. inv st.
  move=>Γ A B s r t i k tyA ihA tyB ihB n o st. inv st.
  { move:(ihA _ o H5)=>tyA'.
    apply: clc_pi...
    destruct s=>//=.
    apply: context_conv.
    apply: conv_sym.
    apply: conv1...
    rewrite<-re_invo.
    rewrite<-pure_re...
    exact: tyB. }
  { destruct s.
    have /ihB{}ihB :(ok [A :U Γ]).
      simpl.
      apply: ty_ok.
      apply: re_ok...
      rewrite<-re_invo.
      rewrite<-pure_re...
    move:(ihB _ H5)=>tyB'.
    apply: clc_pi...
    have /ihB{}ihB :(ok [A :L Γ]).
      simpl.
      apply: n_ok.
      apply: re_ok...
    move:(ihB _ H5)=>tyB'.
    apply: clc_pi... }
  move=>Γ x A s hs n o st. inv st.
  move=>Γ A B m s r t i k tyP ihP tym ihm n o st.
  move:(pi_inv tyP)=>[l[tyA[_ tyB]]]. inv st.
  { have st : Pi A B s r t ~> Pi A' B s r t...
    move:(ihP _ (re_ok o) st)=>tyP'.
    apply: clc_conv.
    apply: conv_sub.
    apply: conv1i...
    apply: clc_lam...
    apply: context_conv.
    apply: conv1i...
    exact: tyA.
    exact: tym.
    exact: tyP. }
  { have: ok (A :{s} Γ)... }
  move=>Γ1 Γ2 Γ A B m n s r t k mrg tym ihm tyn ihn m0 o st.
  move:(merge_context_ok_inv mrg o)=>[o1 o2].
  move:(ihm^~ o1)=>{}ihm.
  move:(ihn^~ o2)=>{}ihn. 
  move:(validity o1 tym)=>[lP tyP]. inv st.
  { move:(lam_inv tyP tym)=>tym1.
    apply: substitution... }
  { move:(ihm _ H2)=>{}ihm.
    apply: clc_app... }
  { move:(ihn _ H2)=>{}ihn.
    move:(pi_inv tyP)=>[l[tyA[_[_ tyB]]]].
    move:(merge_re_re mrg)=>[e1[e2 e3]].
    destruct s.
    { have mrg' : [Γ1] ∘ Γ2 => [Γ].
        replace Γ2 with [Γ2].
        rewrite e2 e3...
        rewrite<-pure_re...
      have {}tyB := substitution tyB k mrg' tyn.
      apply: clc_conv.
      apply: conv_sub.
      apply: conv_beta.
      apply: conv1i...
      apply: clc_app...
      exact: tyB. }
    { have {}tyB := substitutionN tyB tyn.
      apply: clc_conv.
      apply: conv_sub.
      apply: conv_beta.
      apply: conv1i...
      apply: clc_app...
      rewrite<-e2.
      exact: tyB. } }
  move=>Γ A Cs s l k ar cCs tyA ihA tyCs ihCs n wf st. inv st.
  { apply: clc_conv.
    apply: conv_sub.
    apply: conv1i...
    apply: clc_indd...
    apply: arity_step...
    elim: tyCs. constructor.
    move=>C Cs' tyC hd tl.
    constructor...
    apply: context_conv.
    apply: conv1i...
    rewrite<-pure_re...
    eauto.
    rewrite<-pure_re... }
  { apply: clc_indd...
    elim: H3 cCs=>{Cs Cs' tyCs ihCs}.
    { move=>C C' Cs' st h. inv h.
      constructor...
      apply: constr_step... }
    { move=>C Cs Cs' oCs ih h. inv h.
      constructor... }
    elim: H3 tyCs ihCs=>{Cs Cs' cCs}.
    { move=>C C' Cs' st h1 h2. inv h1. inv h2.
      constructor...
      apply: H3...
      apply: ty_ok...
      rewrite<-pure_re... }
    { move=>C C' Cs' st ih h1 h2. inv h1. inv h2.
      constructor... } }
  move=>Γ A s i C Cs I k ig tyI ih n wf st. inv st. inv H2.
  { have st : Ind A Cs s ~> Ind A' Cs s.
    { constructor; eauto. }
    have{}ih:=ih _ wf st.
    have[l[_[_[ar[cCs[tyA tyCs]]]]]]:=ind_inv tyI.
    have[l'[_[_[_[_[tyA' _]]]]]]:=ind_inv ih.
    have tyC:=iget_All1 ig tyCs.
    have//=tyCI:=substitution tyC k (merge_pure k) tyI.
    apply: clc_conv.
    apply: conv_sub.
    apply: conv_beta.
    apply: conv1i...
    apply: clc_constr...
    apply: clc_conv.
    apply: conv_sub.
    apply: conv1...
    eauto.
    rewrite<-pure_re...
    rewrite<-pure_re... }
  { have st : Ind A Cs s ~> Ind A Cs' s.
    { constructor... }
    have{}ih:=ih _ wf st.
    have[l[_[_[ar[cCs[tyA tyCs]]]]]]:=ind_inv tyI.
    have[l'[_[_[_[cCs'[tyA' tyCs']]]]]]:=ind_inv ih.
    have[C' e' ig']:=iget_step ig H4.
    have tyC:=iget_All1 ig tyCs.
    have tyC':=iget_All1 ig' tyCs'.
    have//=tyCI:=substitution tyC k (merge_pure k) tyI.
    have//=tyCI':=substitution tyC' k (merge_pure k) ih.
    have h: C.[I/] === C'.[Ind A Cs' s/].
    { apply: (conv_trans C.[Ind A Cs' s/]).
      apply: conv_beta. apply: conv1...
      apply: conv_subst... }
    apply: clc_conv.
    apply: conv_sub.
    apply: conv_sym...
    apply: clc_constr...
    rewrite<-pure_re... }
  move=>Γ1 Γ2 Γ A Q s s' k Fs Cs m ms I leq ar key mrg
    tym ihm tyQ ihQ tyFs ihFs n wf st. inv st.
  {

  }
  move=>Γ A B m s i sb tym ihm tyB ihB n o st.
  { apply: clc_conv... }
Qed.

Theorem subject_reduction Γ m n A s :
  ok Γ -> Γ ⊢ m : A : s -> m ~>* n -> Γ ⊢ n : A : s.
Proof.
  move=>wf tym rd. elim: rd; eauto.
  move=>y z rd ih st.
  apply: subject_step.
  exact: wf.
  exact: ih.
  exact: st.
Qed.
