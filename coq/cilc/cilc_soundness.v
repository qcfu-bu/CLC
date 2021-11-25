From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion cilc_arity_spine
  cilc_validity cilc_typing_spine cilc_respine cilc_iota_lemma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma arity_step s A A' :
  arity s A -> step A A' -> arity s A'.
Proof.
  move=> a. elim: a A'.
  move=> l A' st. inv st.
  move=> A0 B a ih A' st. inv st.
    constructor; eauto.
    constructor; eauto.
Qed.

Definition n_Beta k (sigma : var -> term) x :=
  k < x.+1 /\
  (forall i, i < k -> sigma i = (Var i)) /\
  (noccurs x (sigma k)) /\
  (forall i, k < i -> (sigma i).[ren (+1)] = Var i).

Lemma noccurs_n_Beta x m :
  noccurs x m -> n_Beta 0 (m .: ids) x.
Proof.
  move=> no.
  firstorder.
  inv H.
  destruct i.
  inv H.
  asimpl; eauto.
Qed.

Lemma n_Beta_up k x sigma :
  n_Beta k sigma x -> n_Beta k.+1 (up sigma) x.+1.
Proof.
  move=> [lt[h1[h2 h3]]].
  firstorder.
  destruct i; asimpl; eauto.
    have lt' : i < k by eauto.
    replace (Var i.+1) with (Var i).[ren (+1)] by eauto.
    f_equal; eauto.
  asimpl.
    apply noccurs_up; eauto.
  destruct i.
    inv H.
    have lt' : k < i by eauto.
    move: (h3 _ lt')=>e; asimpl.
    replace (sigma i).[ren (+2)] 
      with (sigma i).[ren (+1)].[ren (+1)] by autosubst.
    rewrite e; eauto.
Qed.

Lemma lt_False x y : x < y -> y < x.+1 -> False.
Proof.
  elim: x y; intros.
  destruct y.
  inv H.
  inv H0.
  destruct y.
  inv H0.
  eapply H; eauto.
Qed.

Lemma noccurs_Beta k x m sigma :
  noccurs (x.+1) m -> n_Beta k sigma x -> noccurs x m.[sigma].
Proof with eauto using n_Beta_up, lt_False.
  move e:(x.+1)=> i no. move: i m no sigma k x e. 
  apply: noccurs_ind_nested=>//=; intros; subst; try constructor...
  unfold n_Beta in H0; firstorder.
    move: (ltngtP k y)=>[h|h|h].
    move: (H3 _ h)=>e.
    destruct (sigma y); try discriminate.
    inv e.
    constructor; eauto.
    rewrite H1; eauto.
    constructor.
    intro; subst...
    subst; eauto.
  elim: H2=>//=; intros.
    constructor...
  elim: H4=>//=; intros.
    constructor...
  elim: H4=>//=; intros.
    constructor...
Qed.

Lemma noccurs_spine' x h1 h2 ms : 
  noccurs x (spine' h1 ms) -> noccurs x h2 -> noccurs x (spine' h2 ms).
Proof.
  move e:(spine' h1 ms)=> n no. move: x n no h1 h2 ms e.
  apply: noccurs_ind_nested; intros;
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

Lemma noccurs_step x m n :
  noccurs x m -> step m n -> noccurs x n.
Proof with eauto using noccurs, noccurs_Beta, noccurs_n_Beta.
  move=> no. move: x m no n. 
  apply: noccurs_ind_nested; intros;
  match goal with
  | [ H : step _ _ |- _ ] => 
    try solve [inv H; eauto using noccurs]
  end.
  inv H3.
    move: (H0 _ H7)=>no...
    move: (H2 _ H7)=>no...
    inv H...
  inv H3...
    constructor...
    elim: H8 H2 H1=>//=; intros.
      inv H2. inv H3. constructor...
      inv H3. inv H4. constructor...
  inv H5...
    constructor...
      elim: H10 H4 H3=>//=; intros.
        inv H4. inv H5. constructor...
        inv H5. inv H6. constructor...
    apply: noccurs_spine; eauto.
      elim: H10 H3; intros.
        inv H3...
        inv H6...
  inv H5...
    constructor...
      elim: H10 H4 H3=>//=; intros.
        inv H4. inv H5. constructor...
        inv H5. inv H6. constructor...
    apply: noccurs_spine; eauto.
      elim: H10 H3; intros.
        inv H3...
        inv H6...
  inv H3...
Qed.

Lemma head_spine'_step h h' ms :
  step h h' -> step (spine' h ms) (spine' h' ms).
Proof.
  elim: ms h h'; eauto.
  move=> h ms ih h1 h2 st; simpl.
  constructor; eauto.
Qed.

Lemma head_spine'_conv h h' ms :
  h === h' -> spine' h ms === spine' h' ms.
Proof.
  elim: ms h h'; eauto.
  move=> h ms ih h1 h2 e; simpl.
  apply: conv_App; eauto.
Qed.

Lemma head_spine_step h h' ms :
  step h h' -> step (spine h ms) (spine h' ms).
Proof.
  rewrite! spine_spine'_rev=>st.
  apply: head_spine'_step; eauto.
Qed.

Lemma head_spine_conv h h' ms :
  h === h' -> spine h ms === spine h' ms.
Proof.
  rewrite! spine_spine'_rev=>st.
  apply: head_spine'_conv; eauto.
Qed.

Lemma Var_spine'_step x ms C :
  step (spine' (Var x) ms) C ->
  List.Forall (noccurs x) ms ->
  exists ms', 
    C = spine' (Var x) ms' /\ List.Forall (noccurs x) ms'.
Proof.
  elim: ms x C=>//=.
  move=> x C st. inv st.
  move=> a l ih x C st no.
    inv no.
    inv st.
    move: (ih x m' H4 H2)=>[ms'[e no]]; subst.
      exists (a :: ms'); eauto.
    exists (n' :: l); firstorder.
      constructor; eauto.
      apply: noccurs_step; eauto.
    destruct l; inv H0.
Qed.

Lemma noccurs_Forall_cat x ms ns :
  List.Forall (noccurs x) ms ->
  List.Forall (noccurs x) ns ->
  List.Forall (noccurs x) (ms ++ ns).
Proof with eauto using List.Forall.
  move=> no. elim: no ns=>//={ms}...
Qed.

Lemma noccurs_Forall_rev x ms :
  List.Forall (noccurs x) ms -> List.Forall (noccurs x) (rev ms).
Proof with eauto using List.Forall.
  elim: ms=>//=; intros.
  inv H0.
  move: (H H4)=> {}H.
  replace (a :: l) with ([:: a] ++ l) by eauto.
  rewrite rev_cat.
  apply: noccurs_Forall_cat; eauto.
  rewrite /rev/catrev...
Qed.

Lemma Var_spine_step x ms C :
  step (spine (Var x) ms) C ->
  List.Forall (noccurs x) ms ->
  exists ms', 
    C = spine (Var x) ms' /\ List.Forall (noccurs x) ms'.
Proof.
  rewrite! spine_spine'_rev.
  move=> st /noccurs_Forall_rev no.
  move: (Var_spine'_step st no)=>[ms' [h1 h2]].
  exists (rev ms'). split.
  rewrite spine_spine'_rev. rewrite revK; eauto.
  apply noccurs_Forall_rev; eauto.
Qed.

Lemma pos_step x A B :
  pos x A -> step A B -> pos x B.
Proof.
  move=> p. elim: p B=>{A x}.
  move=> x ms no B st.
    move: (Var_spine_step st no)=>[ms'[e no']]; subst.
    constructor; eauto.
  move=> x A B s n p ih B' st. inv st.
    constructor; eauto.
    apply: noccurs_step; eauto.
    constructor; eauto.
  move=> x A B s n p ih B' st. inv st.
    constructor; eauto.
    apply: noccurs_step; eauto.
    constructor; eauto.
Qed.

Lemma active_step x C C' :
  active x C -> step C C' -> active x C'.
Proof.
  move=> a. elim: a C'=>{C x}.
  move=> x ms no C' st.
    move: (Var_spine_step st no)=>[ms'[e no']]; subst.
    apply: active_X; eauto.
  move=> x A B s p a ih no C' st. inv st.
    apply: active_Pos; eauto.
    apply: pos_step; eauto.
    apply: active_Pos; eauto.
    apply: noccurs_step; eauto.
  move=> x A B s n a ih C' st. inv st.
    apply: active_Lolli; eauto.
    apply: noccurs_step; eauto.
    apply: active_Lolli; eauto.
Qed.

Lemma constr_step x s C C' :
  constr x s C -> step C C' -> constr x s C'.
Proof.
  move=> c. elim: c C'=>{C x s}.
  move=> x s ms no C' st.
    move: (Var_spine_step st no)=>[ms'[e no']]; subst.
    apply: constr_X; eauto.
  move=> x A B p c ih no C' st. inv st.
    apply: constr_UPos; eauto.
    apply: pos_step; eauto.
    apply: constr_UPos; eauto.
    apply: noccurs_step; eauto.
  move=> x A B n c ih C' st. inv st.
    apply: constr_UProd; eauto.
    apply: noccurs_step; eauto.
    apply: constr_UProd; eauto.
  move=> x A B p c ih n C' st. inv st.
    apply: constr_LPos1; eauto.
    apply: pos_step; eauto.
    apply: constr_LPos1; eauto.
    apply: noccurs_step; eauto.
  move=> x A B p a n C' st. inv st.
    apply: constr_LPos2; eauto.
    apply: pos_step; eauto.
    apply: constr_LPos2; eauto.
    apply: active_step; eauto.
    apply: noccurs_step; eauto.
  move=> x A B n c ih C' st. inv st.
    apply: constr_LProd1; eauto.
    apply: noccurs_step; eauto.
    apply: constr_LProd1; eauto.
  move=> x A B n a C' st. inv st.
    apply: constr_LProd2; eauto.
    apply: noccurs_step; eauto.
    apply: constr_LProd2; eauto.
    apply: active_step; eauto.
Qed.

Lemma iget_step i Cs Cs' C :
  iget i Cs C -> One2 step Cs Cs' -> 
    exists C', C === C' /\ iget i Cs' C'.
Proof.
  move=> ig h. elim: h i ig=>{Cs Cs'}.
  move=> m m' Cs st i ig. inv ig.
    exists m'. split.
      apply: conv1; eauto.
      constructor.
    exists C. split; eauto.
      constructor; eauto.
  move=> m Cs Cs' h ih i ig. inv ig.
    exists C. repeat constructor.
    move: (ih _ H3)=>[C' [e ig]].
    exists C'. repeat constructor; eauto.
Qed.

Lemma respine_step Q Q' C :
  step Q Q' -> step (respine Q C) (respine Q' C).
Proof.
  elim: C Q Q'=>//=.
  move=> A ihA B ihB s Q Q' st.
    constructor.
    apply: ihB.
    apply: step_subst; eauto.
  move=> A ihA B ihB s Q Q' st.
    constructor.
    apply: ihB.
    apply: step_subst; eauto.
  move=> m ihM n ihN Q Q' st.
    constructor; eauto.
Qed.

Lemma drespine_step Q Q' c C :
  step Q Q' -> step (drespine Q c C) (drespine Q' c C).
Proof with eauto using step.
  elim: C Q Q' c...
  move=> A ihA B ihB s Q Q' c cst.
    constructor.
    apply: ihB.
    apply: step_subst; eauto.
  move=> A ihA B ihB s Q Q' c st.
    constructor.
    apply: respine_step; eauto.
  move=> m ihM n ihN Q Q' c st.
    constructor.
    apply: respine_step; eauto.
Qed.

Lemma case_step I Q Q' C :
  step Q Q' -> step (case I Q C) (case I Q' C).
Proof.
  move=>st. unfold case.
  apply: respine_step; eauto.
Qed.

Lemma All2_case_stepQ Gamma A Q Q' Fs Cs Cs' s t l :
  let I := Ind A Cs' s in
  step Q Q' ->
  arity s A ->
  [ re Gamma |- I :- A ] ->
  [ re Gamma |- Q' :- arity1 t A ] ->
  All2 (fun F C => constr 0 s C /\ 
    [ Gamma |- F :- case I Q C ]) Fs Cs ->
  List.Forall (fun C => [ A +u re Gamma |- C :- U @ l ]) Cs ->
  All2 (fun F C => constr 0 s C /\
    [ Gamma |- F :- case I Q' C ]) Fs Cs.
Proof.
  move=> I st a tyInd tyQ all. elim: all=>{Fs Cs}.
  constructor.
  move=> F C Fs Cs [c tyF] hd tl h.
  inv h.
  constructor; eauto.
  firstorder.
  have h1 : (I .: ids) 0 = Ind A Cs' s by eauto.
  have //=h2 : [re Gamma |- C.[I/] :- (U @ l).[I/]].
    apply: substitutionU; eauto.
    apply: re_pure.
    apply: merge_re_re_re.
  have h3 : respine Q C.[I/] <: respine Q' C.[I/].
    apply: conv_sub.
    apply: conv1.
    apply: respine_step; eauto.
  move: 
  (@constr_respine Gamma (I .: ids) Cs' A Q' C 0 U s t l c a h1
    tyInd tyQ h2)=>[s0[l0 tySp]].
  unfold case.
  unfold case in tyF.
  apply: s_Conv.
  apply: h3.
  apply: tySp.
  apply: tyF.
Qed.

Inductive sub_list : nat -> list term -> list term -> Prop :=
| sub_list_O xs : sub_list 0 xs xs
| sub_list_S x xs ys n : 
  sub_list n xs ys -> sub_list n.+1 (x :: xs) ys.

Lemma sub_list_iget i XS x xs :
  sub_list i XS (x :: xs) -> iget i XS x.
Proof.
  move e:(x :: xs)=> ys sb.
  elim: sb x xs e=>{i XS ys}; intros; subst.
  { constructor. }
  { constructor.
    apply: H0; eauto. }
Qed.

Lemma sub_list_ok i XS x xs :
  sub_list i XS (x :: xs) -> sub_list i.+1 XS xs.
Proof.
  move e:(x :: xs)=> ys sb.
  elim: sb x xs e=>{i XS ys}; intros; subst.
  { repeat constructor. }
  { constructor.
    apply: H0; eauto. }
Qed.

Lemma All2i_strengthen (P : nat -> term -> term -> Prop) Cs Fs Xs n :
  All2i (fun i F C => P i F C) n Fs Xs ->
  sub_list n Cs Xs ->
  All2i (fun i F C => iget i Cs C /\ P i F C) n Fs Xs.
Proof.
  move=> a2i. elim: a2i Cs=>{Fs Xs n}; intros.
  { constructor. }
  { constructor.
    { apply sub_list_iget in H2; eauto. }
    { apply: H1.
      apply: sub_list_ok; eauto. } }
Qed.

Lemma All2i_dcase_stepQ Gamma A Q Q' Fs Cs Xs n s l :
  let I := Ind A Cs U in
  step Q Q' ->
  arity U A ->
  [ re Gamma |- I :- A ] ->
  [ re Gamma |- Q' :- arity2 s I A ] ->
  sub_list n Cs Xs ->
  All2i (fun i F C => constr 0 U C /\ 
    [ Gamma |- F :- dcase I Q (Constr i I) C ]) n Fs Xs ->
  List.Forall (fun C => [ A +u re Gamma |- C :- U @ l ]) Xs ->
  All2i (fun i F C => constr 0 U C /\
    [ Gamma |- F :- dcase I Q' (Constr i I) C ]) n Fs Xs.
Proof.
  move=> I st a tyInd tyQ sb a2i. 
  move: (All2i_strengthen a2i sb)=>{sb}a2i. elim: a2i=>{Fs Xs}.
  constructor.
  move=> i F C Fs Cs' [c tyF] hd tl h; subst.
  inv h.
  constructor; eauto.
  firstorder.
  have h1 : (I .: ids) 0 = Ind A Cs U by eauto.
  have //=h2 : [re Gamma |- C.[I/] :- (U @ l).[I/]].
    apply: substitutionU; eauto.
    apply: re_pure.
    apply: merge_re_re_re.
  have h3 : drespine Q (Constr i I) C.[I/] <: drespine Q' (Constr i I) C.[I/].
    apply: conv_sub.
    apply: conv1.
    apply: drespine_step; eauto.
  have h4 : [re Gamma |- Constr i I :- C.[I/]].
    apply: s_Constr; eauto.
    apply: re_pure.
  pose proof
  (@constr_drespine Gamma (I .: ids) Cs A Q' C (Constr i I) 0 s U l
    H a h1 tyInd tyQ h2 h4); firstorder.
  unfold dcase.
  apply: s_Conv.
  apply: h3.
  apply: H4.
  apply: H0.
Qed.

Lemma All2_One2_stepF Gamma A Q Fs Fs' Cs Cs' s :
  let I := Ind A Cs' s in
  [ Gamma |- ] ->
  One2 step Fs Fs' ->
  All2 (fun F C => constr 0 s C /\ 
    [ Gamma |- F :- case I Q C ]) Fs Cs ->
  All2 (fun F C => constr 0 s C /\ ([ Gamma |- ] -> 
    forall F', step F F' -> [ Gamma |- F' :- case I Q C ])) Fs Cs ->
  All2 (fun F C => constr 0 s C /\
    [ Gamma |- F :- case I Q C ]) Fs' Cs.
Proof.
  move=> I wf one. elim: one Cs=>{Fs Fs'}.
  move=> F F' Fs' st Cs hd tl.
    inv hd. inv tl.
    constructor; eauto.
    constructor; firstorder; eauto.
  move=> F Fs Fs' one ih Cs hd tl.
    inv hd. inv tl.
    constructor; eauto.
Qed.

Lemma All2i_One2_stepF Gamma A Q Fs Fs' Cs Cs' n s :
  let I := Ind A Cs' s in
  [ Gamma |- ] ->
  One2 step Fs Fs' ->
  All2i (fun i F C => constr 0 s C /\ 
    [ Gamma |- F :- dcase I Q (Constr i I) C ]) n Fs Cs ->
  All2i (fun i F C => constr 0 s C /\ ([ Gamma |- ] -> forall F', 
    step F F' -> [ Gamma |- F' :- dcase I Q (Constr i I) C ])) n Fs Cs ->
  All2i (fun i F C => constr 0 s C /\
    [ Gamma |- F :- dcase I Q (Constr i I) C ]) n Fs' Cs.
Proof.
  move=> I wf one. elim: one Cs n=>{Fs Fs'}.
  move=> F F' Fs' st Cs n hd tl.
    inv hd. inv tl.
    constructor; eauto.
    constructor; firstorder; eauto.
  move=> F Fs Fs' one ih Cs n hd tl.
    inv hd. inv tl.
    constructor; eauto.
Qed.

Theorem subject_reduction Gamma m A :
  [ Gamma |- ] ->
  [ Gamma |- m :- A ] ->
  forall n, step m n -> [ Gamma |- n :- A ].
Proof.
  move=> wf ty.
  move: Gamma m A ty wf. apply: has_type_nested_ind.
  { move=> Gamma s l p wf n st. inv st. }
  { move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    { move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: u_Prod; eauto.
      apply: context_convU.
      apply: e.
      rewrite <- pure_re; eauto.
      apply: tyB. }
    { have {}wf : [ A +u Gamma |- ].
      apply: u_ok; eauto.
      rewrite <- pure_re; eauto.
      move: (ihB wf _ H3)=>tyB'.
      apply: u_Prod; eauto. } }
  { move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    { move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: l_Prod; eauto. }
    { have {}wf : [ +n Gamma |- ].
      apply: n_ok; eauto.
      move: (ihB wf _ H3)=>tyB'.
      apply: l_Prod; eauto. } }
  { move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    { move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: u_Lolli; eauto.
      apply: context_convU.
      apply: e.
      rewrite <- pure_re; eauto.
      apply: tyB. }
    { have {}wf : [ A +u Gamma |- ].
      apply: u_ok; eauto.
      rewrite <- pure_re; eauto.
      apply: u_Lolli; eauto. } }
  { move=> Gamma A B s l p tyA ihA tyB ihB wf n st. inv st.
    { move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: l_Lolli; eauto. }
    { have {}wf : [ +n Gamma |- ].
      apply: n_ok; eauto.
      move: (ihB wf _ H3)=>tyB'.
      apply: l_Lolli; eauto. } }
  { move=> Gamma x A hA wf n st. inv st. }
  { move=> Gamma x A hA wf n st. inv st. }
  { move=> Gamma n A B s t l p tyProd ihProd tyN ihN wf n' st. inv st.
    { have stProd : step (Prod A B s) (Prod A' B s).
      by constructor.
      move: (ihProd wf _ stProd)=>tyProd'.
      apply: s_Conv.
        apply: conv_sub. 
        apply: conv_sym. 
        apply: conv1; eauto.
        rewrite <- pure_re; eauto.
      apply: u_Lam; eauto.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      destruct s.
        move: tyProd=>/u_Prod_inv[_[lA[_[tyA _]]]].
          apply: context_convU.
          apply: e.
          rewrite <- pure_re; eauto.
          apply: tyN.
        move: tyProd=>/l_Prod_inv[_[lA[_[tyA _]]]].
          apply: context_convL.
          apply: e.
          rewrite <- pure_re; eauto.
          apply: tyN. }
    { destruct s.
      move: (u_Prod_inv tyProd)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A +u Gamma |- ].
          apply: u_ok; eauto.
          rewrite <- pure_re; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: u_Lam; eauto.
      move: (l_Prod_inv tyProd)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A+l Gamma |- ].
          apply: l_ok; eauto.
          rewrite <- pure_re; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: u_Lam; eauto. } }
  { move=> Gamma n A B s t l tyLolli ihLolli tyN ihN wf n' st. inv st.
    { have stLolli : step (Lolli A B s) (Lolli A' B s).
      by constructor.
      have {}wf : [ re Gamma |- ].
        apply: re_ok; eauto.
      move: (ihLolli wf _ stLolli)=>tyLolli'.
      apply: s_Conv.
        apply: conv_sub.
        apply: conv_sym.
        apply: conv1; eauto.
        apply: tyLolli.
      apply: l_Lam; eauto.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      destruct s.
        move: tyLolli=>/u_Lolli_inv[_[lA[_[tyA _]]]].
          apply: context_convU.
          apply: e.
          apply: tyA.
          apply: tyN.
        move: tyLolli=>/l_Lolli_inv[_[lA[_[tyA _]]]].
          apply: context_convL.
          apply: e.
          apply: tyA.
          apply: tyN. }
    { destruct s.
      move: (u_Lolli_inv tyLolli)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A +u Gamma |- ].
          apply: u_ok; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: l_Lam; eauto.
      move: (l_Lolli_inv tyLolli)=>[_[lA[_[tyA _]]]].
        have {}wf : [ A +l Gamma |- ].
          apply: l_ok; eauto.
        move: (ihN wf _ H3)=>tyM'.
        apply: l_Lam; eauto. } }
  { move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (pure_re p)=> e3.
    move: (validity wf1 tyM)=>[s[l tyProd]].
    inv st.
    { move: (ihM _ H2)=>{H2}ihM.
      apply: u_Prod_App; eauto. }
    { move: (ihN _ H2)=>{}ihN.
      move: (u_Prod_inv tyProd)=>[sB[lB[_ [_ [tyB _]]]]].
      have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
        apply: substitutionU; eauto.
        rewrite e3 e2 e1.
        apply: merge_re_re_re.
      have e : B.[n'0/] === B.[n/].
        apply: conv_Beta.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: e.
      rewrite <- e1; eauto.
      apply: u_Prod_App; eauto. }
    { move: (u_Lam_inv tyProd tyM)=>tyM0.
      apply: substitutionU; eauto. } }
  { move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (validity wf1 tyM)=>[s[l tyProd]].
    inv st.
    { move: (ihM _ H2)=>{H2}ihM.
      apply: l_Prod_App; eauto. }
    { move: (ihN _ H2)=>{}ihN.
      move: (l_Prod_inv tyProd)=>[sB[lB[_ [_ [tyB _]]]]].
      have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
        apply: substitutionN; eauto.
      have e : B.[n'0/] === B.[n/].
        apply: conv_Beta.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: e.
      rewrite <- e1; eauto.
      apply: l_Prod_App; eauto. }
    { move: (u_Lam_inv tyProd tyM)=>tyM0.
      apply: substitutionL; eauto. } }
  { move=> Gamma1 Gamma2 Gamma A B m n p tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (pure_re p)=> e3.
    move: (validity wf1 tyM)=>[s[l tyLolli]].
    inv st.
    { move: (ihM _ H2)=>{H2}ihM.
        apply: u_Lolli_App; eauto. }
    { move: (ihN _ H2)=>{}ihN.
      move: (u_Lolli_inv tyLolli)=>[sB[lB[_ [_ [tyB _]]]]].
      have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
        apply: substitutionU; eauto.
        rewrite e3 e2 e1.
        apply: merge_re_re_re.
      have e : B.[n'0/] === B.[n/].
        apply: conv_Beta.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: e.
      rewrite <- e1; eauto.
      apply: u_Lolli_App; eauto. }
    { move: (l_Lam_inv tyLolli tyM)=>tyM0.
      apply: substitutionU; eauto. } }
  { move=> Gamma1 Gamma2 Gamma A B m n tyM ihM tyN ihN mg wf n' st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (ihM wf1)=>{}ihM.
    move: (ihN wf2)=>{}ihN.
    move: (merge_re_re mg)=>[e1 e2].
    move: (validity wf1 tyM)=>[s[l tyLolli]].
    inv st.
    { move: (ihM _ H2)=>{H2}ihM.
      apply: l_Lolli_App; eauto. }
    { move: (ihN _ H2)=>{}ihN.
      move: (l_Lolli_inv tyLolli)=>[sB[lB[_ [_ [tyB _]]]]].
      have //={}tyB : [ re Gamma1 |- B.[n/] :- (sB @ lB).[n/] ].
        apply: substitutionN; eauto.
      have e : B.[n'0/] === B.[n/].
        apply: conv_Beta.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: e.
      rewrite <- e1; eauto.
      apply: l_Lolli_App; eauto. }
    { move: (l_Lam_inv tyLolli tyM)=>tyM0.
      apply: substitutionL; eauto. } }
  { move=> Gamma A s Cs l a cs p tyA ihA tyCs ihCs wf n st. inv st.
    { move: (ihA wf _ H3)=>tyA'.
      have e : A' === A.
        apply: conv_sym.
        apply: conv1; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: e.
      rewrite <- pure_re; eauto.
      apply: s_Ind; eauto.
      apply: arity_step; eauto.
      elim: tyCs=>//=; intros.
        constructor; eauto.
        apply: context_convU.
        apply: e.
        rewrite <- pure_re; eauto.
        apply: H. }
    { apply: s_Ind; eauto.
      elim: H3 cs; intros.
        inv cs. constructor; eauto.
          apply: constr_step; eauto.
        inv cs. constructor; eauto.
      elim: H3 tyCs ihCs; intros.
        inv tyCs. inv ihCs. constructor; eauto.
          apply: H4; eauto. apply: u_ok; eauto. rewrite <- pure_re; eauto.
        inv tyCs. inv ihCs. constructor; eauto. } } 
  { move=> Gamma A s i C Cs I ig p tyI ihI wf n st. inv st. inv H2.
    { have st : step (Ind A Cs s) (Ind A' Cs s).
        constructor; eauto.
      have e : Ind A' Cs s === Ind A Cs s.
        apply: conv_sym. apply: conv1; eauto.
      move: (ihI wf _ st)=>ihI'.
      move: (s_Ind_inv tyI)=>[l[a[cs[_[tyA tyCs]]]]].
      move: (s_Ind_invX ihI')=>[l'[_[_[_[_[tyA' _]]]]]].
      move: (iget_Forall ig tyCs)=>tyC.
      have mg : merge Gamma Gamma Gamma.
        apply: merge_pure; eauto.
      move: (substitutionU tyC tyI p mg)=>tyCI.
      apply: s_Conv.
      apply: conv_sub. apply: conv_Beta. apply: e.
      rewrite <- pure_re; eauto.
      constructor; eauto.
      apply: s_Conv. apply: conv_sub. apply: conv1; eauto.
      rewrite <- pure_re; eauto.
      apply: ihI'. }
    { have st : step (Ind A Cs s) (Ind A Cs' s).
        constructor; eauto.
      have e : Ind A Cs' s === Ind A Cs s.
        apply: conv_sym. apply: conv1; eauto.
      move: (ihI wf _ st)=>ihI'.
      move: (s_Ind_inv tyI)=>[l[a[cs[_[tyA tyCs]]]]].
      move: (s_Ind_inv ihI')=>[l'[_[cs'[_[tyA' tyCs']]]]].
      move: (iget_step ig H4)=>[C' [e' ig']].
      move: (iget_Forall ig tyCs)=>tyC.
      move: (iget_Forall ig' tyCs')=>tyC'.
      have mg : merge Gamma Gamma Gamma.
        apply: merge_pure; eauto.
      move: (substitutionU tyC tyI p mg)=>//=tyCI.
      move: (substitutionU tyC' ihI' p mg)=>//=tyCI'.
      have ex : C.[Ind A Cs s/] === C'.[Ind A Cs' s/].
        apply: (conv_trans C.[Ind A Cs' s/]).
        apply: conv_Beta. apply: conv_sym; eauto.
        apply: conv_subst; eauto.
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply: ex.
      rewrite <- pure_re; eauto.
      constructor; eauto. } } 
  { move=> Gamma1 Gamma2 Gamma A Q s s' Fs Cs m ms I a mg 
    tyM ihM tyQ ihQ tyFsCs ihFsCs wf n st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].
    move: (validity wf1 tyM)=>[sI[lI tyI]].
    inv st.
    { move: (ihM wf1 _ H3)=>{}ihM.
      econstructor; eauto. }
    { move: (re_ok wf2)=>rwf2.
      move: (ihQ rwf2 _ H3)=>{}ihQ.
      have p : pure (re Gamma1).
        apply: re_pure.
      move: (s_Ind_spine_inv p a tyI)=>[sA[lA sp]].
      move: (@arity1_spine (re Gamma1) ms A sA s s' lA sp a p)=>{}sp.
      rewrite e2 in tyQ. rewrite <- e1 in tyQ.
      rewrite e2 in ihQ. rewrite <- e1 in ihQ.
      move: (merge_re_re_re Gamma1)=>mg1.
      move: (App_arity_spine tyQ sp mg1)=>tySp.
      move: (App_arity_spine ihQ sp mg1)=>tySp'.
      have e : step (spine Q ms) (spine Q' ms).
        apply: head_spine_step; eauto.
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply: conv1; eauto.
      rewrite <-e1; eauto.
      econstructor; eauto.
      rewrite e2. rewrite <-e1; eauto.
      move: (s_Ind_spine p tyI)=>tyInd.
      move: (s_Ind_inv tyInd)=>[l[_[cs[_[tyA tyCs]]]]].
      apply: All2_case_stepQ; eauto.
      rewrite e2; rewrite <-e1; eauto.
      rewrite e2; rewrite <-e1; eauto.
      rewrite e2; rewrite <-e1; eauto. }
    { econstructor; eauto.
      apply: All2_One2_stepF; eauto. }
    { have p : pure (re Gamma1).
        apply: re_pure.
      move: (s_Ind_spine p tyI)=>tyInd.
      move: (spine_inv wf1 tyM)=>[Gamma3[Gamma4[X[mgX[tyC0 tySp]]]]].
      move: (s_Constr_invX tyC0)=>[A'[C'[Cs'[s0[ig[p'[e[sb tyM']]]]]]]]; subst.
      move: (merge_pure1 mgX p')=>e; subst.
      move: (s_Ind_inv tyM')=>[l[a'[cs[_[tyA' tyCs']]]]].
      move: (s_Ind_inv tyInd)=>[l0[aA[_[p4[tyA tyCs]]]]].
      move: (iget_Forall ig tyCs')=>tyC'.
      move: (merge_context_ok_inv mgX wf1)=>[wf3 wf4].
      move: (merge_re_re mgX)=>[e _].
      move: (validity wf3 tyC0)=>[sX[lX tyX]].
      rewrite e in tyX.
      move: (typing_spine_strengthen tySp sb tyX)=>{}tySp.
      move: (iget_Forall ig cs)=>c.
      have ex : (Ind A' Cs' s0 .: ids) 0 = Ind A' Cs' s0 by eauto.
      move: (typing_spine_constr_Ind c tySp ex)=>//=cv.
      move: (iget_All2 tyFsCs H3)=>[C[igC[cC tyF]]].
      move: (Ind_inj cv)=>[eA[a2Cs es]]; subst.
      move: (iget_All2 a2Cs ig)=>[Cx[igCx eCx]].
      move: (iget_iget igCx igC)=>eC; subst.
      have eCI : C.[Ind A Cs s/] <: C'.[Ind A' Cs' s/].
        apply: conv_sub.
        apply: conv_trans.
        apply: conv_Beta.
        apply: conv_sym.
        apply: cv.
        apply: conv_subst.
        apply: conv_sym.
        apply: eCx.
      have mg3 : merge Gamma3 Gamma3 Gamma3.
        apply: merge_pure; eauto.
      move: (substitutionU tyC' tyM' p' mg3)=>//=tyCI.
      have {}tyCI' : [ re Gamma3 |- C'.[Ind A' Cs' s/] :- U @ l ].
        rewrite<-pure_re; eauto.
      rewrite e in tyCI'.
      move: (typing_spine_strengthen tySp eCI tyCI')=>{}tySp.
      move: (s_Ind_spine_inv p a tyI)=>[s1[l1 arSp]].
      move: (arity1_spine s' arSp a p)=>{}arSp.
      move: (merge_re_re_re Gamma4)=>mg4.
      rewrite e2 in tyQ. rewrite<-e1 in tyQ.
      move: (App_arity_spine tyQ arSp mg4)=>tySQ.
      move: (iget_Forall igC tyCs)=>tyC.
      have {}tyCI : [ re Gamma4 |- C.[Ind A Cs s/] :- U @ l0 ].
        replace (U @ l0) with (U @ l0).[Ind A Cs s/] by eauto.
        apply: substitutionU; eauto.
      have h1 : (Ind A Cs s .: ids) 0 = Ind A Cs s by eauto.
      have h2 : forall x, ~(Ind A Cs s .: ids) 0 = Var x.
        discriminate.
      pose proof 
      (@typing_spine_constr1 Gamma4 A Cs C (Ind A Cs s .: ids) 
        Q ms0 ms U s s' s' l1 l0 0 cC tySp h1 h2 tyCI tyInd tyQ tySQ).
      apply: App_typing_spine.
      apply: tyF.
      apply: H.
      apply: merge_sym; eauto. } }
  { move=> Gamma1 Gamma2 Gamma A Q s Fs Cs m ms I a p mg 
    tyM ihM tyQ ihQ tyFsCs ihFsCs wf n st.
    move: (merge_context_ok_inv mg wf)=>[wf1 wf2].
    move: (merge_re_re mg)=>[e1 e2].
    move: (validity wf1 tyM)=>[sI[lI tyI]].
    inv st.
    { move: (ihM wf1 _ H3)=>{}ihM.
      have sb : App (spine Q ms) m' <: App (spine Q ms) m.
      { apply: conv_sub.
        apply: conv_sym.
        apply: conv1.
        constructor; eauto. }
      have pr : pure (re Gamma1) by apply re_pure.
      have {}tyI : [re Gamma1 |- spine (Ind A Cs U) ms :- sI @ lI].
        by eauto.
      move: (s_Ind_spine_inv pr a tyI)=>[s0[l tySp]].
      move: (s_Ind_spine pr tyI)=>{}tyI.
      move: (arity2_spine s tySp a pr tyI)=>{}tySp.
      have mg' : merge (re Gamma2) (re Gamma1) (re Gamma).
        rewrite e1 e2. apply: merge_re_re_re.
      move: (App_arity_spine tyQ tySp mg')=>tySQ.
      have {}tyM : [ re Gamma1 |- m :- spine I ms ].
        rewrite<-pure_re; eauto.
      rewrite<-e2 in tySQ.
      move: (u_Prod_App pr tySQ tyM mg')=>//=tyApp.
      apply: s_Conv; eauto.
      apply: s_DCase; eauto.
      rewrite<-pure_re; eauto.
      rewrite<-pure_re; eauto. }
    { move: (re_ok wf2)=>rwf2.
      move: (ihQ rwf2 _ H3)=>{}ihQ.
      have pr : pure (re Gamma1).
        apply: re_pure.
      move: (s_Ind_spine_inv pr a tyI)=>[sA[lA sp]].
      move: (s_Ind_spine pr tyI)=>{}tyI.
      move: (arity2_spine s sp a pr tyI)=>{}sp.
      rewrite e2 in tyQ. rewrite <- e1 in tyQ.
      rewrite e2 in ihQ. rewrite <- e1 in ihQ.
      move: (merge_re_re_re Gamma1)=>mg1.
      move: (App_arity_spine tyQ sp mg1)=>tySp.
      move: (App_arity_spine ihQ sp mg1)=>tySp'.
      have e : step (spine Q ms) (spine Q' ms).
        apply: head_spine_step; eauto.
      have {}tyM : [ re Gamma1 |- m :- spine I ms ].
        rewrite<-pure_re; eauto.
      have mg' := merge_re_re_re Gamma1.
      move: (u_Prod_App pr tySp tyM mg')=>//=tyApp.
      apply: s_Conv.
      apply: conv_sub. apply: conv_sym. apply: conv1.
      apply: step_AppL; eauto.
      rewrite e1 in tyApp; eauto.
      apply: {pr}s_DCase; eauto.
      rewrite<-pure_re in tyM; eauto.
      rewrite e2. rewrite <-e1; eauto.
      move: (s_Ind_inv tyI)=>[l[_[cs[_[tyA tyCs]]]]].
      apply: All2i_dcase_stepQ; eauto.
      rewrite e2; rewrite <-e1; eauto.
      rewrite e2; rewrite <-e1; eauto.
      constructor.
      rewrite e2; rewrite <-e1; eauto. }
    { econstructor; eauto.
      apply: All2i_One2_stepF; eauto. }
    { have pr : pure (re Gamma1).
        apply: re_pure.
      move: (s_Ind_spine pr tyI)=>tyInd.
      move: (spine_inv wf1 tyM)=>[Gamma3[Gamma4[X[mgX[tyC0 tySp]]]]].
      move: (s_Constr_invX tyC0)=>[A'[C'[Cs'[s0[ig[p'[e[sb tyM']]]]]]]]; subst.
      move: (merge_pure1 mgX p')=>e; subst.
      move: (s_Ind_inv tyM')=>[l[a'[cs[_[tyA' tyCs']]]]].
      move: (s_Ind_inv tyInd)=>[l0[aA[_[p4[tyA tyCs]]]]].
      move: (iget_Forall ig tyCs')=>tyC'.
      move: (merge_context_ok_inv mgX wf1)=>[wf3 wf4].
      move: (merge_re_re mgX)=>[e _].
      move: (validity wf3 tyC0)=>[sX[lX tyX]].
      rewrite e in tyX.
      move: (typing_spine_strengthen tySp sb tyX)=>{}tySp.
      move: (iget_Forall ig cs)=>c.
      have ex : (Ind A' Cs' s0 .: ids) 0 = Ind A' Cs' s0 by eauto.
      move: (typing_spine_constr_Ind c tySp ex)=>//=cv.
      move: (iget_All2i tyFsCs H3)=>[C[igC[cC tyF]]].
      move: (Ind_inj cv)=>[eA[a2Cs es]]; subst.
      move: (iget_All2 a2Cs ig)=>[Cx[igCx eCx]].
      move: (iget_iget igCx igC)=>eC; subst.
      have eCI : C.[Ind A Cs U/] <: C'.[Ind A' Cs' U/].
        apply: conv_sub.
        apply: conv_trans.
        apply: conv_Beta.
        apply: conv_sym.
        apply: cv.
        apply: conv_subst.
        apply: conv_sym.
        apply: eCx.
      have mg3 : merge Gamma3 Gamma3 Gamma3.
        apply: merge_pure; eauto.
      move: (substitutionU tyC' tyM' p' mg3)=>//=tyCI.
      have {}tyCI' : [ re Gamma3 |- C'.[Ind A' Cs' U/] :- U @ l ].
        rewrite<-pure_re; eauto.
      rewrite e in tyCI'.
      move: (typing_spine_strengthen tySp eCI tyCI')=>{}tySp.
      move: (s_Ind_spine_inv pr a tyI)=>[s1[l1 arSp]].
      move: (arity2_spine s arSp a pr tyInd)=>{}arSp.
      move: (merge_re_re_re Gamma4)=>mgr4.
      have mg4 : merge Gamma4 Gamma4 Gamma4.
        apply: merge_pure; eauto.
      rewrite e2 in tyQ. rewrite<-e1 in tyQ.
      move: (App_arity_spine tyQ arSp mgr4)=>tySQ.
      rewrite<-pure_re in tySQ; eauto.
      move: (iget_Forall igC tyCs)=>tyC.
      have {}tyCI : [ re Gamma4 |- C.[Ind A Cs U/] :- U @ l0 ].
        replace (U @ l0) with (U @ l0).[Ind A Cs U/] by eauto.
        apply: substitutionU; eauto.
      have h1 : (Ind A Cs U .: ids) 0 = Ind A Cs U by eauto.
      have h2 : forall x, ~(Ind A Cs U .: ids) 0 = Var x.
        discriminate.
      have h3 : App (spine Q ms) (spine (Constr i (Ind A Cs U)) ms0) <:
                App (spine Q ms) (spine (Constr i (Ind A' Cs' U)) ms0).
        apply: conv_sub.
        apply: conv_App; eauto.
        apply: head_spine_conv.
        apply: conv_Constr.
        apply: conv_sym; eauto.
      have h4 : [ Gamma4 |- Constr i I :- C.[I/] ].
        constructor; eauto.
        rewrite<-pure_re in tyInd; eauto.
      have //=h5 := u_Prod_App p tySQ tyM mg4.
      apply: s_Conv.
      apply: h3.
      rewrite<-e1.
      rewrite<-pure_re; eauto.
      rewrite add0n in tyF.
      unfold dcase in tyF.
      apply: App_typing_spine.
      apply: tyF.
      2:{ apply: merge_sym; eauto. }
      apply: typing_spine_constr2; eauto.
      rewrite<-pure_re; eauto.
      rewrite<-pure_re; eauto. } }
  { move=> Gamma A m l p tyA ihA tyM ihM wf n st. inv st.
    { have {}ihA := ihA wf _ H2.
      have h : [ A +u re Gamma |- A'.[ren (+1)] :- (U @ l).[ren (+1)] ].
        apply: eweakeningU; eauto.
        rewrite<-pure_re; eauto.
      apply: s_Conv.
      apply: conv_sub.
      apply: conv_sym.
      apply: conv1; eauto.
      rewrite<-pure_re; eauto.
      apply: u_Fix; eauto.
      apply: context_convU.
      apply: conv_sym.
      apply: conv1; eauto.
      rewrite<-pure_re; eauto.
      apply: s_Conv.
      apply: sub_subst.
      apply: conv_sub.
      apply: conv1; eauto.
      apply: h.
      apply: tyM. }
    { have {}wf : [ A +u Gamma |- ].
        apply: u_ok; eauto.
        rewrite<-pure_re; eauto.
      have {}ihM := ihM wf _ H2.
      apply: u_Fix; eauto. }
    { have tyFix : [ Gamma |- Fix A m :- A ].
        apply: u_Fix; eauto.
      have mg := merge_pure p.
      have h := substitutionU tyM tyFix p mg.
      asimpl in h; eauto. } }
  { move=> Gamma A B m s l sb tyB ihB tyM ihM wf m' st.
    apply: s_Conv; eauto. }
Qed.