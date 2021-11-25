From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Program Utf8 Classical.
Require Import AutosubstSsr ARS 
  cilc_context cilc_ast cilc_confluence cilc_subtype cilc_typing 
  cilc_weakening cilc_substitution cilc_inversion cilc_arity_spine
  cilc_validity cilc_typing_spine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma respine_spine'_Ind Q A Cs s ms :
  respine Q (spine' (Ind A Cs s) ms) = spine' Q ms.
Proof.
  elim: ms; simpl; intros; eauto.
  rewrite H; eauto.
Qed.

Lemma drespine_spine'_Ind Q A Cs c s ms :
  drespine Q c (spine' (Ind A Cs s) ms) = App (spine' Q ms) c.
Proof.
  elim: ms; simpl; intros; eauto.
  rewrite respine_spine'_Ind; eauto.
Qed.

Lemma respine_spine_Ind Q A Cs s ms :
  respine Q (spine (Ind A Cs s) ms) = spine Q ms.
Proof.
  rewrite! spine_spine'_rev.
  apply: respine_spine'_Ind.
Qed.

Lemma drespine_spine_Ind Q A Cs c s ms :
  drespine Q c (spine (Ind A Cs s) ms) = App (spine Q ms) c.
Proof.
  rewrite! spine_spine'_rev.
  apply: drespine_spine'_Ind.
Qed.

Lemma spine'_Var x y ms :
  spine' (Var x) ms = Var y -> x = y /\ ms = nil.
Proof.
  elim: ms; simpl; intros.
  inv H; eauto.
  inv H0.
Qed.

Lemma app_False (ls : list term) x :
  ls ++ [:: x] = nil -> False.
Proof.
  elim: ls; simpl; intros.
  inv H.
  inv H0.
Qed.

Lemma rev_nil (ls : list term) :
  rev ls = nil -> ls = nil.
Proof.
  destruct ls; eauto.
  replace (t :: ls) with ([:: t] ++ ls) by eauto.
  rewrite rev_cat.
  rewrite /rev/catrev=>h.
  exfalso.
  apply: app_False; eauto.
Qed.

Lemma spine_Var x y ms :
  spine (Var x) ms = Var y -> x = y /\ ms = nil.
Proof.
  rewrite spine_spine'_rev=> /spine'_Var[-> e].
  firstorder.
  apply: rev_nil; eauto.
Qed.

Lemma has_type_Lam_False Γ A B C s l :
  [ Γ |- Lam A B U :- C ] -> C <: s @ l -> False.
Proof.
  move e1:(Lam A B U)=> m ty.
  move: Γ m C ty A B s l e1.
  apply: has_type_nested_ind; intros; 
  try (discriminate || solve[exfalso; solve_sub]).
  subst.
  apply: H3; eauto.
  apply: sub_trans; eauto.
Qed.

Lemma has_type_Ind_False Γ X Cs A B C r s t l :
  [ Γ |- Ind X Cs s :- C ] -> C <: Prod A B r ->
  [ Γ |- Ind X Cs s :- t @ l ] -> False.
Proof.
  move e:(Ind X Cs s)=>I ty.
  move: Γ I C ty X Cs A B r s t l e.
  apply: has_type_nested_ind; try discriminate; intros.
  - inv e.
    apply s_Ind_invX in H7. firstorder.
    inv H8.
    clear H7.
    exfalso; solve_sub.
    clear H6.
    exfalso; solve_sub.
  - subst.
    apply: H3; eauto.
    apply: sub_trans; eauto.
Qed.

Ltac solve_spine' :=
  match goal with
  | [ H : spine' _ ?ms = _ |- ?x ] =>
    destruct ms; simpl in H; intros;
    match goal with
    | [ H : _ = ?x |- _ ] => inv H
    end
  | [ H : _ = spine' _ ?ms |- ?x ] =>
    destruct ms; simpl in H; intros;
    match goal with
    | [ H : ?x = _ |- _ ] => inv H
    end
  end.

Ltac solve_spine :=
  match goal with
  | [ H : spine _ _ = _ |- _ ] =>
    rewrite spine_spine'_rev in H; solve_spine'
  | [ H : _ = spine _ _ |- _ ] =>
    rewrite spine_spine'_rev in H; solve_spine'
  end.

Lemma active_respine Γ I Cs A Q C n r s t l :
  active n C ->
  arity s A ->
  (I n = Ind A Cs s) ->
  [ re Γ |- I n :- A ] ->
  [ re Γ |- Q :- arity1 t A ] ->
  [ re Γ |- C.[I] :- r @ l ] ->
  exists s l,
    [ re Γ |- respine Q C.[I] :- s @ l ].
Proof.
  elim: C Γ I Cs A Q n r s t l; simpl; intros;
  match goal with
  | [ H : active _ _ |- _ ] => 
    try solve [inv H; exfalso; solve_spine]
  end.
  { inv H.
    move: (spine_Var H5)=>[e _]; subst. inv H0.
    { exists t. exists l0. rewrite H1; eauto. }
    { rewrite H1 in H2. 
      rewrite H1 in H4.
      exfalso.
      apply: has_type_Ind_False.
      apply: H2.
      eauto.
      apply: H4. } }
  { specialize
    (@H0 (A.[I] +{s} Γ) (up I) 
      Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] n.+1).
    inv H1; try solve[exfalso; solve_spine]; destruct s. 
    { move: (u_Lolli_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H3. autosubst.
      have h3 : [ A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [ A.[I] +u re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H12 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (l_Lolli_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H3. autosubst.
      have h3 : [ +n re Γ |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningN; eauto.
      have h4 : [ +n re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H12 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure. }
    { move: (u_Lolli_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H3. autosubst.
      have h3 : [ A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [ A.[I] +u re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H12 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (l_Lolli_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity s0 A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] s0.
        asimpl. rewrite H3. autosubst.
      have h3 : [ +n re Γ |- up I n.+1 :- A0.[ren (+1)] ].
        asimpl. apply: eweakeningN; eauto.
      have h4 : [ +n re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)] ].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' s0 t l1 H12 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure. } }
  { inv H1.
    replace (App (respine Q m.[I]) n.[I]) 
      with (respine Q (App m n).[I]) by eauto.
    replace (App m.[I] n.[I]) with (App m n).[I] in H6 by eauto.
    rewrite <-H7.
    rewrite <-H7 in H6.
    rewrite spine_subst; simpl.
    rewrite spine_subst in H6; simpl in H6.
    rewrite H3.
    rewrite H3 in H6.
    have p : pure (re Γ).
      apply: re_pure.
    move: (s_Ind_spine_inv p H2 H6)=>[s0[l0 tySp]].
    move: (arity1_spine t tySp H2 p)=>{}tySp.
    move: (merge_re_re_re Γ)=>mg.
    move: (App_arity_spine H5 tySp mg)=>tyQ.
    rewrite respine_spine_Ind.
    exists t. exists l0; eauto. }
Qed.

Lemma constr_respine Γ I Cs A Q C n r s t l :
  constr n s C ->
  arity s A ->
  (I n = Ind A Cs s) ->
  [ re Γ |- I n :- A ] ->
  [ re Γ |- Q :- arity1 t A ] ->
  [ re Γ |- C.[I] :- r @ l ] ->
  exists s l,
    [ re Γ |- respine Q C.[I] :- s @ l ].
Proof.
  elim: C Γ I Cs A Q n r s t l; simpl; intros;
  match goal with
  | [ H : constr _ _ _ |- _ ] => 
    try solve [inv H; exfalso; solve_spine]
  end.
  { inv H.
    move: (spine_Var H5)=>[e _]; subst. inv H0.
    { exists t. exists l0. rewrite H1; eauto. }
    { rewrite H1 in H2.
      rewrite H1 in H4. 
      exfalso. 
      apply: has_type_Ind_False.
      apply: H2.
      eauto.
      apply: H4. } }
  { specialize (@H0 (A.[I] +{s} Γ) (up I) 
      Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] n.+1).
    inv H1; try solve[exfalso; solve_spine].
    { move: (u_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity U A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U).
        asimpl. rewrite H3. autosubst.
      have h3 : [A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [A.[I] +u re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' U t l1 H13 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (u_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity U A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U).
        asimpl. rewrite H3. autosubst.
      have h3 : [A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [A.[I] +u re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' U t l1 H13 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (u_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H3. autosubst.
      have h3 : [A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [A.[I] +u re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' L t l1 H13 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (l_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H3. autosubst.
      have h3 : [ re (A.[I] +l Γ) |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningN; eauto.
      have h4 : [ re (A.[I] +l Γ) |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (active_respine H13 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure. }
    { move: (u_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H3. autosubst.
      have h3 : [A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [A.[I] +u re Γ |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity1_ren; eauto.
      move: (@H0 s' L t l1 H13 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (l_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity L A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] L).
        asimpl. rewrite H3. autosubst.
      have h3 : [ re (A.[I] +l Γ) |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningN; eauto.
      have h4 : [ re (A.[I] +l Γ) |- Q.[ren (+1)] :- arity1 t A0.[ren (+1)]].
        apply: eweakeningN; eauto.
        erewrite arity1_ren; eauto.
      move: (active_respine H13 h1 h2 h3 h4 tyB)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: l_Lolli_max; eauto.
      apply: re_pure. } }
  { inv H1.
    replace (App (respine Q m.[I]) n.[I])
      with (respine Q (App m n).[I]) by eauto.
    replace (App m.[I] n.[I]) with (App m n).[I] in H6 by eauto.
    rewrite <- H7.
    rewrite <- H7 in H6.
    rewrite spine_subst; simpl.
    rewrite spine_subst in H6; simpl in H6.
    rewrite H3.
    rewrite H3 in H6.
    have p : pure (re Γ).
      apply: re_pure.
    move: (s_Ind_spine_inv p H2 H6)=>[s0[l0 tySp]].
    move: (arity1_spine t tySp H2 p)=>{}tySp.
    move: (merge_re_re_re Γ)=> mg.
    move: (App_arity_spine H5 tySp mg)=>tyQ.
    rewrite respine_spine_Ind.
    exists t. exists l0; eauto. }
Qed.

Lemma constr_drespine Γ I Cs A Q C c n s r l :
  constr n U C ->
  arity U A ->
  (I n = Ind A Cs U) ->
  [ re Γ |- I n :- A ] ->
  [ re Γ |- Q :- arity2 s (Ind A Cs U) A ] ->
  [ re Γ |- C.[I] :- r @ l ] ->
  [ re Γ |- c :- C.[I] ] ->
  exists s l,
    [ re Γ |- drespine Q c C.[I] :- s @ l ].
Proof.
  elim: C Γ I Cs A Q c n s r l; simpl; intros;
  match goal with
  | [ H : constr _ _ _ |- _ ] => 
    try solve [inv H; exfalso; solve_spine]
  end.
  { inv H.
    move: (spine_Var H6)=>[e _]; subst. inv H0.
    { exists s. exists l0. rewrite H1; simpl; simpl in H3.
      rewrite H1 in H5.
      replace (s @ l0) with (s @ l0).[c/] by eauto.
      apply: u_Prod_App; eauto.
      apply: re_pure.
      apply: merge_re_re_re. }
    { rewrite H1 in H2.
      rewrite H1 in H4. 
      exfalso. 
      apply: has_type_Ind_False.
      apply: H2.
      eauto.
      apply: H4. } }
  { specialize (@H0 (A.[I] +{s} Γ) (up I) 
    Cs..[up (ren (+1))] A0.[ren (+1)] Q.[ren (+1)] (App c.[ren (+1)] (Var 0)) n.+1).
    inv H1; try solve[exfalso; solve_spine].
    { move: (u_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity U A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U).
        asimpl. rewrite H3. autosubst.
      have h3 : [A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [A.[I] +u re Γ |- Q.[ren (+1)] :- 
        arity2 s0 (Ind A0 Cs U).[ren (+1)] A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity2_ren; eauto.
      have h5 : [A.[I] +u re Γ |- c.[ren (+1)] :- 
        (Prod A.[I] B.[up I] U).[ren (+1)]].
        apply: eweakeningU; eauto.
      asimpl in h5.
      have h6 : [A.[I] +u re Γ |- ids 0 :- A.[I].[ren (+1)]].
        apply: u_Var.
        constructor.
        apply: re_pure.
      asimpl in h6.
      have pr : pure (A.[I] +u re Γ).
        constructor.
        apply: re_pure.
      pose proof (merge_re_re_re (A.[I] +u Γ)).
      simpl in H1.
      have h7 := u_Prod_App pr h5 h6 H1.
      asimpl in h7.
      move: (@H0 s0 s' l1 H13 h1 h2 h3 h4 tyB h7)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. }
    { move: (u_Prod_inv H6)=>[s'[l1[l2[tyA[tyB sb]]]]].
      have h1 : arity U A0.[ren (+1)].
        apply: arity_ren; eauto.
      have h2 : (up I n.+1 = Ind A0.[ren (+1)] Cs..[up (ren (+1))] U).
        asimpl. rewrite H3. autosubst.
      have h3 : [A.[I] +u re Γ |- up I n.+1 :- A0.[ren (+1)]].
        asimpl. apply: eweakeningU; eauto.
      have h4 : [A.[I] +u re Γ |- Q.[ren (+1)] :- 
        arity2 s0 (Ind A0 Cs U).[ren (+1)] A0.[ren (+1)]].
        apply: eweakeningU; eauto.
        erewrite arity2_ren; eauto.
      have h5 : [A.[I] +u re Γ |- c.[ren (+1)] :- 
        (Prod A.[I] B.[up I] U).[ren (+1)]].
        apply: eweakeningU; eauto.
      asimpl in h5.
      have h6 : [A.[I] +u re Γ |- ids 0 :- A.[I].[ren (+1)]].
        apply: u_Var.
        constructor.
        apply: re_pure.
      asimpl in h6.
      have pr : pure (A.[I] +u re Γ).
        constructor.
        apply: re_pure.
      pose proof (merge_re_re_re (A.[I] +u Γ)).
      simpl in H1.
      have h7 := u_Prod_App pr h5 h6 H1.
      asimpl in h7.
      move: (@H0 s0 s' l1 H13 h1 h2 h3 h4 tyB h7)=>[s[l0 tySp]].
      exists L. exists (maxn l1 l0).
      apply: u_Lolli_max; eauto.
      apply: re_pure. } }
  { inv H1.
    replace (App (respine Q m.[I]) n.[I])
      with (respine Q (App m n).[I]) by eauto.
    replace (App m.[I] n.[I]) with (App m n).[I] in H6 by eauto.
    replace (App m.[I] n.[I]) with (App m n).[I] in H7 by eauto.
    rewrite <- H8.
    rewrite <- H8 in H6.
    rewrite <- H8 in H7.
    rewrite spine_subst; simpl.
    rewrite spine_subst in H6; simpl in H6.
    rewrite spine_subst in H7; simpl in H7.
    rewrite H3.
    rewrite H3 in H6.
    rewrite H3 in H7.
    have p : pure (re Γ).
      apply: re_pure.
    move: (s_Ind_spine_inv p H2 H6)=>[s0[l0 tySp]].
    move: (s_Ind_spine p H6)=>tyI.
    move: (arity2_spine s tySp H2 p tyI)=>{}tySp.
    move: (merge_re_re_re Γ)=> mg.
    move: (App_arity_spine H5 tySp mg)=>tyQ.
    rewrite respine_spine_Ind.
    exists s. exists l0. 
    replace (s @ l0) with (s @ l0).[c/] by eauto.
    apply: u_Prod_App; eauto. }
Qed.