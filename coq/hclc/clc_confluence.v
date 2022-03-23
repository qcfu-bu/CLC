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
| pstep_pi A A' B B' s r t :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi A B s r t) 
        (Pi A' B' s r t)
| pstep_unit :
  pstep Unit Unit
| pstep_it :
  pstep It It
| pstep_bool :
  pstep Bool Bool
| pstep_left :
  pstep Left Left
| pstep_right :
  pstep Right Right
| pstep_sigma A A' B B' s r t :
  pstep A A' ->
  pstep B B' ->
  pstep (Sigma A B s r t) (Sigma A' B' s r t)
| pstep_pair m m' n n' t :
  pstep m m' ->
  pstep n n' ->
  pstep (Pair m n t) (Pair m' n' t)
| pstep_case m m' n1 n1' n2 n2' :
  pstep m m' ->
  pstep n1 n1' ->
  pstep n2 n2' ->
  pstep (Case m n1 n2) (Case m' n1' n2')
| pstep_iotaL n1 n1' n2 :
  pstep n1 n1' ->
  pstep (Case Left n1 n2) n1'
| pstep_iotaR n1 n2 n2' :
  pstep n2 n2' ->
  pstep (Case Right n1 n2) n2'
| pstep_letin1 m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (LetIn1 m n) (LetIn1 m' n')
| pstep_iota1 n n' :
  pstep n n' ->
  pstep (LetIn1 It n) n'
| pstep_letin2 m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (LetIn2 m n) (LetIn2 m' n')
| pstep_iota2 m1 m1' m2 m2' n n' t :
  pstep m1 m1' ->
  pstep m2 m2' ->
  pstep n n' ->
  pstep (LetIn2 (Pair m1 m2 t) n) n'.[m2',m1'/]
| pstep_ptr l :
  pstep (Ptr l) (Ptr l).

Definition sred σ τ :=
  forall x : var, (σ x) ~>* (τ x).

Lemma step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using step.
  move=> A m n s t σ. 
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply step_beta. autosubst.
  move=> m1 m2 n t σ.
    replace (n.[m2,m1/].[σ]) with (n.[upn 2 σ].[m2.[σ],m1.[σ]/])
      by autosubst.
    apply: step_iota2.
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

Lemma red_pi A A' B B' s r t :
  A ~>* A' -> B ~>* B' -> Pi A B s r t ~>* Pi A' B' s r t.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi A' B s r t)).
  apply: (star_hom ((((Pi^~ B)^~ s)^~ r)^~ t)) r1=>x y. exact: step_piL.
  apply: (star_hom ((((Pi A')^~ s)^~ r)^~ t)) r2=>x y. exact: step_piR.
Qed.

Lemma red_sigma A A' B B' s r t :
  A ~>* A' -> B ~>* B' -> Sigma A B s r t ~>* Sigma A' B' s r t.
Proof.
  move=>r1 r2.
  apply: (star_trans (Sigma A' B  s r t)).
  apply: (star_hom ((((Sigma^~ B)^~ s)^~ r)^~ t)) r1=>x y. 
    exact: step_sigmaL.
  apply: (star_hom ((((Sigma A')^~ s)^~ r)^~ t)) r2=>x y.
    exact: step_sigmaR.
Qed.

Lemma red_pair m m' n n' t :
  m ~>* m' -> n ~>* n' -> Pair m n t ~>* Pair m' n' t.
Proof.
  move=>r1 r2.
  apply: (star_trans (Pair m' n t)).
  apply: (star_hom ((Pair^~ n)^~ t)) r1=>x y. exact: step_pairL.
  apply: (star_hom ((Pair m')^~ t)) r2=>x y. exact: step_pairR.
Qed.

Lemma red_case m m' n1 n1' n2 n2' :
  m ~>* m' -> n1 ~>* n1' -> n2 ~>* n2' -> Case m n1 n2 ~>* Case m' n1' n2'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (Case m' n1 n2)).
  apply: (star_hom ((Case^~ n1)^~ n2)) r1=>x y. exact: step_caseL.
  apply: (star_trans (Case m' n1' n2)).
  apply: (star_hom ((Case m')^~ n2)) r2=>x y. exact: step_caseR1.
  apply: (star_hom (Case m' n1')) r3=> x y. exact: step_caseR2.
Qed.

Lemma red_letin1 m m' n n' :
  m ~>* m' -> n ~>* n' -> LetIn1 m n ~>* LetIn1 m' n'.
Proof.
  move=>r1 r2.
  apply: (star_trans (LetIn1 m' n)).
  apply: (star_hom (LetIn1^~ n)) r1=>x y. exact: step_letin1L.
  apply: (star_hom (LetIn1 m')) r2=>x y. exact: step_letin1R.
Qed.

Lemma red_letin2 m m' n n' :
  m ~>* m' -> n ~>* n' -> LetIn2 m n ~>* LetIn2 m' n'.
Proof.
  move=>r1 r2.
  apply: (star_trans (LetIn2 m' n)).
  apply: (star_hom (LetIn2^~ n)) r1=>x y. exact: step_letin2L.
  apply: (star_hom (LetIn2 m')) r2=>x y. exact: step_letin2R.
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

Lemma sred_upn n σ τ : sred σ τ -> sred (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sred_up. by asimpl.
Qed.

Hint Resolve 
  red_app red_lam red_pi red_sigma
  red_case red_pair red_letin1 red_letin2
  sred_up sred_upn : red_congr.

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

Lemma conv_pi A A' B B' s r t :
  A === A' -> B === B' -> Pi A B s r t === Pi A' B' s r t.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi A' B s r t)).
  apply: (conv_hom ((((Pi^~ B)^~ s)^~ r)^~ t)) r1=>x y. exact: step_piL.
  apply: (conv_hom ((((Pi A')^~ s)^~ r)^~ t)) r2=>x y. exact: step_piR.
Qed.

Lemma conv_sigma A A' B B' s r t :
  A === A' -> B === B' -> Sigma A B s r t === Sigma A' B' s r t.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Sigma A' B  s r t)).
  apply: (conv_hom ((((Sigma^~ B)^~ s)^~ r)^~ t)) r1=>x y. 
    exact: step_sigmaL.
  apply: (conv_hom ((((Sigma A')^~ s)^~ r)^~ t)) r2=>x y.
    exact: step_sigmaR.
Qed.

Lemma conv_pair m m' n n' t :
  m === m' -> n === n' -> Pair m n t === Pair m' n' t.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Pair m' n t)).
  apply: (conv_hom ((Pair^~ n)^~ t)) r1=>x y. exact: step_pairL.
  apply: (conv_hom ((Pair m')^~ t)) r2=>x y. exact: step_pairR.
Qed.

Lemma conv_case m m' n1 n1' n2 n2' :
  m === m' -> n1 === n1' -> n2 === n2' -> Case m n1 n2 === Case m' n1' n2'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (Case m' n1 n2)).
  apply: (conv_hom ((Case^~ n1)^~ n2)) r1=>x y. exact: step_caseL.
  apply: (conv_trans (Case m' n1' n2)).
  apply: (conv_hom ((Case m')^~ n2)) r2=>x y. exact: step_caseR1.
  apply: (conv_hom (Case m' n1')) r3=> x y. exact: step_caseR2.
Qed.

Lemma conv_letin1 m m' n n' :
  m === m' -> n === n' -> LetIn1 m n === LetIn1 m' n'.
Proof.
  move=>r1 r2.
  apply: (conv_trans (LetIn1 m' n)).
  apply: (conv_hom (LetIn1^~ n)) r1=>x y. exact: step_letin1L.
  apply: (conv_hom (LetIn1 m')) r2=>x y. exact: step_letin1R.
Qed.

Lemma conv_letin2 m m' n n' :
  m === m' -> n === n' -> LetIn2 m n === LetIn2 m' n'.
Proof.
  move=>r1 r2.
  apply: (conv_trans (LetIn2 m' n)).
  apply: (conv_hom (LetIn2^~ n)) r1=>x y. exact: step_letin2L.
  apply: (conv_hom (LetIn2 m')) r2=>x y. exact: step_letin2R.
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

Lemma sconv_upn n σ τ : sconv σ τ -> sconv (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sconv_up. by asimpl.
Qed.

Hint Resolve
  conv_app conv_lam conv_pi conv_sigma
  conv_case conv_pair conv_letin1 conv_letin2
  sconv_up sconv_upn : conv_congr.

Lemma conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto with conv_congr. Qed.

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
  move=> A m m' n n' s t p1 r1 p2 r2. 
    apply: starES. by constructor.
    apply: (star_trans (m'.[n.:Var])). exact: red_subst.
    by apply: red_compat => -[|].
  move=>n1 n1' n2 p r.
    apply: starES. by constructor. exact: r.
  move=>n1 n2 n2' p r.
    apply: starES. by constructor. exact: r.
  move=>n n' p1 r1.
    apply: starES. by constructor. exact: r1.
  move=>m1 m1' m2 m2' n n' t p1 r1 p2 r2 pn rn.
    apply: starES. by constructor.
    apply: (star_trans n'.[m2,m1/]).
    by apply: red_subst.
    by apply: red_compat=>-[|-[]].
Qed.

Lemma pstep_subst s t σ : pstep s t -> pstep s.[σ] t.[σ].
Proof with eauto using pstep, pstep_refl.
  move=>ps.
    elim: ps σ=>{s t}...
  move=>A m m' n n' s t ps1 ih1 ps2 ih2 σ.
    asimpl.
    specialize (ih1 (up σ)).
    specialize (ih2 σ).
    have:=pstep_beta A.[σ] s t ih1 ih2.
    by asimpl.
  move=>m1 m1' m2 m2' n n' t p1 ih1 p2 ih2 pn ihn σ.
    asimpl.
    specialize (ih1 σ).
    specialize (ih2 σ).
    specialize (ihn (upn 2 σ)).
    have:=(pstep_iota2 t ih1 ih2 ihn).
    by asimpl.
Qed.

Definition psstep (σ τ : var -> term) := 
  forall x, pstep (σ x) (τ x).

Lemma psstep_refl σ : psstep σ σ.
Proof with eauto using pstep_refl. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma psstep_upn n σ τ : psstep σ τ -> psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ pss. by asimpl.
  move=>n ihn σ τ /ihn/psstep_up. by asimpl.
Qed.

Lemma pstep_compat s t σ τ :
  pstep s t -> psstep σ τ -> pstep s.[σ] t.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=> ps. elim: ps σ τ=>{s t}...
  move=> A m m' n n' s t ps1 ih1 ps2 ih2 σ τ pss.
    asimpl.
    have {}ih1:=ih1 _ _ (psstep_up pss).
    have {}ih2:=ih2 _ _ pss.
    have:=pstep_beta A.[σ] s t ih1 ih2.
    by asimpl.
  move=>m1 m1' m2 m2' n n' t p1 ih1 p2 ih2 pn ihn σ τ pss.
    have {}ih1:=ih1 _ _ pss.
    have {}ih2:=ih2 _ _ pss.
    have {}ihn:=ihn _ _ (psstep_upn 2 pss).
    have:=pstep_iota2 t ih1 ih2 ihn.
    by asimpl.
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
Proof with eauto 6 using 
  pstep, pstep_refl, 
  pstep_compat, pstep_compat_beta, 
  psstep_compat, psstep_refl.
  move=>ps. elim: ps m2=>{m m1}.
  move=> x m2 p.
    inv p.
    exists (Var x)...
  move=> s l m2 p.
    inv p.
    exists (s @ l)...
  move=> A A' n n' s t pA ihA pn ihn m2 p.
    inv p.
    have[A0 pA1 pA2]:=ihA _ H4.
    have[n0 pn1 pn2]:=ihn _ H5.
    exists (Lam A0 n0 s t)...
  move=> m m' n n' pm ihm pn ihn m2 p.
    inv p.
    have[m0 pm1 pm2]:=ihm _ H1.
    have[n0 pn1 pn2]:=ihn _ H3.
    exists (App m0 n0)...
    inv pm.
    have[n0 pn1 pn2]:=ihn _ H3.
    have pL : pstep (Lam A m0 s t) (Lam A' m'0 s t)...
    have[x px1 px2]:=ihm _ pL.
    inv px1. inv px2.
    exists (n'2.[n0/])...
  move=> A m m' n n' s t pm ihm pn ihn m2 p.
    inv p. inv H1.
    have[mx pm1 pm2]:=ihm _ H7.
    have[nx pn1 pn2]:=ihn _ H3.
    exists (mx.[nx/])...
    have[mx pm1 pm2]:=ihm _ H5.
    have[nx pn1 pn2]:=ihn _ H6.
    exists (mx.[nx/])...
  move=> A A' B B' s r t pA ihA pB ihB m2 p.
    inv p.
    have[Ax pA1 pA2]:=ihA _ H5.
    have[Bx pB1 pB2]:=ihB _ H6.
    exists (Pi Ax Bx s r t)...
  move=>m2 p. inv p. exists Unit...
  move=>m2 p. inv p. exists It...
  move=>m2 p. inv p. exists Bool...
  move=>m2 p. inv p. exists Left...
  move=>m2 p. inv p. exists Right...
  move=>A A' B B' s r t pA ihA pB ihB m2 p.
    inv p.
    have[Ax pA1 pA2]:=ihA _ H5.
    have[Bx pB1 pB2]:=ihB _ H6.
    exists (Sigma Ax Bx s r t)...
  move=>m m' n n' t pm ihm pn ihn m2 p. 
    inv p.
    have[mx pm1 pm2]:=ihm _ H3.
    have[nx pn1 pn2]:=ihn _ H4.
    exists (Pair mx nx t)...
  move=>m m' n1 n1' n2 n2' pm ihm p1 ih1 p2 ih2 m2 p.
    inv p.
    have[mx pm1 pm2]:=ihm _ H2.
    have[x px1 px2]:=ih1 _ H4.
    have[y py1 py2]:=ih2 _ H5.
    exists (Case mx x y)...
    inv pm.
    have[x px1 px2]:=ih1 _ H3.
    exists x...
    inv pm.
    have[y py1 py2]:=ih2 _ H3.
    exists y...
  move=>n1 n1' n2 pn ih m2 p.
    inv p. inv H2.
    have[x px1 px2]:=ih _ H4.
    exists x...
    have[x px1 px2]:=ih _ H2.
    exists x...
  move=>n1 n2 n2' pn ih m2 p.
    inv p. inv H2.
    have[x px1 px2]:=ih _ H5.
    exists x...
    have[x px1 px2]:=ih _ H2.
    exists x...
  move=>m m' n n' pm ihm pn ihn m2 p. 
    inv p.
    have[mx pm1 pm2]:=ihm _ H1.
    have[nx pn1 pn2]:=ihn _ H3.
    exists (LetIn1 mx nx)...
    inv pm.
    have[nx pn1 pn2]:=ihn _ H2.
    exists nx...
  move=>n n' pn ihn m2 p. 
    inv p. inv H1.
    have[nx pn1 pn2]:=ihn _ H3.
    exists nx...
    have[nx pn1 pn2]:=ihn _ H0.
    exists nx...
  move=>m m' n n' pm ihm pn ihn m2 p.
    inv p.
    have[mx pm1 pm2]:=ihm _ H1.
    have[nx pn1 pn2]:=ihn _ H3.
    exists (LetIn2 mx nx)...
    inv pm.
    have{ihn}[nx pn1 pn2]:=ihn _ H4.
    have{}/ihm[mx p1 p2]:pstep (Pair m1 m0 t) (Pair m1' m2' t)...
    inv p1. inv p2.
    exists (nx.[n'2,m'/])...
  move=>m1 m1' m2 m2' n n' p1 t ih1 p2 ih2 pn ihn m0 p.
    inv p. inv H1.
    have[mx1 p11 p12]:=ih1 _ H5.
    have[mx2 p21 p22]:=ih2 _ H6.
    have[nx pn1 pn2]:=ihn _ H3.
    exists (nx.[mx2,mx1/])...
    have[mx1 p11 p12]:=ih1 _ H4.
    have[mx2 p21 p22]:=ih2 _ H5.
    have[nx pn1 pn2]:=ihn _ H6.
    exists (nx.[mx2,mx1/])...
  move=>l m2 p. inv p. exists (Ptr l)...
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

Lemma red_pi_inv A B s r t x :
  Pi A B s r t ~>* x -> 
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi A' B' s r t.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd [A'[B'[r1[r2 e]]]] st; subst.
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
  elim=>//{} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma red_lam_inv A m x s t :
  Lam A m s t ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam A' m' s t.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma red_unit_inv m : Unit ~>* m -> m = Unit.
Proof. elim=>//y z r->p. inv p. Qed.

Lemma red_it_inv m : It ~>* m -> m = It. 
Proof. elim=>//y z r->p. inv p. Qed.

Lemma red_bool_inv m : Bool ~>* m -> m = Bool.
Proof. elim=>//y z r->p. inv p. Qed.

Lemma red_left_inv m : Left ~>* m -> m = Left.
Proof. elim=>//y z r->p. inv p. Qed.

Lemma red_right_inv m : Right ~>* m -> m = Right.
Proof. elim=>//y z r->p. inv p. Qed.

Lemma red_sigma_inv A B s r t x :
  Sigma A B s r t ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Sigma A' B' s r t.
Proof.
  elim.
  exists A. exists B=>//.
  move=>y z r1 [Ax[Bx[rA[rB->]]]] s1. inv s1.
  exists A'. exists Bx. firstorder.
  apply: star_trans. exact: rA. by apply: star1.
  exists Ax. exists B'. firstorder.
  apply: star_trans. exact: rB. by apply: star1.
Qed.

Lemma red_pair_inv m n t x :
  Pair m n t ~>* x ->
  exists m' n',
    m ~>* m' /\ n ~>* n' /\ x = Pair m' n' t.
Proof.
  elim.
  exists m. exists n=>//.
  move=>y z r [mx[nx[rm[rn->]]]] p. inv p.
  exists m'. exists nx. firstorder.
  apply: star_trans. exact: rm. by apply: star1.
  exists mx. exists n'. firstorder.
  apply: star_trans. exact: rn. by apply: star1.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  s1 @ l1 === s2 @ l2 -> s1 = s2 /\ l1 = l2.
Proof.
  move/church_rosser=>[x/red_sort_inv->/red_sort_inv[->->]]//.
Qed.

Lemma pi_inj A A' B B' s s' r r' t t' :
  Pi A B s r t === Pi A' B' s' r' t' -> 
    A === A' /\ B === B' /\ s = s' /\ r = r' /\ t = t'.
Proof.
  move/church_rosser=>
    [x/red_pi_inv[A1[B1[rA1[rB1->]]]]
      /red_pi_inv[A2[B2[rA2[rB2[]]]]]] eA eB es er et; subst.
  repeat split.
  apply: conv_trans.
    apply: star_conv. by apply: rA1.
    apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
    apply: star_conv. by apply: rB1.
    apply: conv_sym. by apply: star_conv.
Qed.

Lemma sigma_inj A A' B B' s s' r r' t t' :
  Sigma A B s r t === Sigma A' B' s' r' t' ->
  A === A' /\ B === B' /\ s = s' /\ r = r' /\ t = t'.
Proof.
  move/church_rosser=>
    [x/red_sigma_inv[A1[B1[rA1[rB1->]]]]]
      /red_sigma_inv[A2[B2[rA2[rB2[]]]]] eA eB es er et; subst.
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
  | Unit  => apply red_unit_inv in H
  | It    => apply red_it_inv in H
  | Bool  => apply red_bool_inv in H
  | Left  => apply red_left_inv in H
  | Right => apply red_right_inv in H
  | Sigma => apply red_sigma_inv in H
  | Pair  => apply red_pair_inv in H
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
  | [ H : red ?m _ |- _ ] => red_inv m H
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
