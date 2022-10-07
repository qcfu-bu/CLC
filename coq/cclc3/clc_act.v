From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Utf8 Classical.
Require Export clc_linearity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma decide_act X ξ :
  (forall r A B s, ~X.[ren ξ] = Act r A B s) \/
  (exists r A B s, X = Act r A B s).
Proof.
  destruct X.
  all: try solve[
    left; intros; intro;
    match goal with
    | [ H : (_).[ren _] = _ |- _ ] => inv H
    end].
  right.
  exists r. exists X. exists B. exists s. eauto.
Qed.

Ltac destruct_ren :=
  repeat match goal with
  | [ H : (?X).[ren _] = _ |- _ ] =>
    destruct X; inv H
  end.

Definition can_cancel (f : var -> var) :=
  exists g, f >>> g = id.

Lemma can_cancel_up f :
  can_cancel f -> can_cancel (upren f).
Proof.
  move=>[g h].
  exists (upren g).
  asimpl.
  rewrite h.
  by asimpl.
Qed.

Lemma can_cancel1 : can_cancel (+1).
Proof.
  exists (subn^~1).
  f_ext. move=>[|x]; asimpl=>//.
Qed.

Lemma can_cancel2 : can_cancel (+2).
Proof.
  exists (subn^~2).
  f_ext. move=>[|x]; asimpl=>//.
Qed.

Lemma step_ren_inv X Y ξ :
  X.[ren ξ] ~> Y.[ren ξ] -> can_cancel ξ -> X ~> Y.
Proof.
  move=>st [g h].
  pose proof (step_subst (ren g) st).
  asimpl in H.
  rewrite h in H.
  by asimpl in H.
Qed.

Lemma red_ren_inv X Y ξ :
  X.[ren ξ] ~>* Y.[ren ξ] -> can_cancel ξ -> X ~>* Y.
Proof.
  move=>st [g h].
  pose proof (red_subst (ren g) st).
  asimpl in H.
  rewrite h in H.
  by asimpl in H.
Qed.

Lemma conv_ren_inv X Y ξ :
  X.[ren ξ] === Y.[ren ξ] -> can_cancel ξ -> X === Y.
Proof.
  move=>st [g h].
  pose proof (conv_subst (ren g) st).
  asimpl in H.
  rewrite h in H.
  by asimpl in H.
Qed.

Lemma dual_step X Y ξ :
  X.[ren ξ] ~> Y ->
  (exists Z,
    Y = Z.[ren ξ] /\ forall r A B s, ~Y = Act r A B s) \/
  (exists r A B s,
    Y = (Act r A B s).[ren ξ]).
Proof.
  elim: X Y ξ.
  all: try solve[
    intros;
    match goal with
    | [ H : _ ~> _ |- _ ] => inv H
    end].
  move=>A ihA B ihB s t Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihA _ _ H4; subst.
    left. exists (Pi Z1 B s t).
    split; eauto.
    intros; intro. inv H.
    left. exists (Pi (Act r1 A1 B1 s1) B s t).
    split; eauto.
    intros; intro. inv H. }
  { asimpl in H4.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihB _ _ H4; subst.
    left. exists (Pi A Z1 s t).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (Pi A (Act r1 A1 B1 s1) s t).
    split; asimpl; eauto.
    intros; intro. inv H. }
  move=>A ihA m ihm s t Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihA _ _ H4; subst.
    left. exists (Lam Z1 m s t).
    split; eauto.
    intros; intro. inv H.
    left. exists (Lam (Act r1 A1 B1 s1) m s t).
    split; eauto.
    intros; intro. inv H. }
  { asimpl in H4.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H4; subst.
    left. exists (Lam A Z1 s t).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (Lam A (Act r1 A1 B1 s1) s t).
    split; asimpl; eauto.
    intros; intro. inv H. }
  move=>m ihm n ihn Y ξ st. inv st.
  { destruct m; inv H0.
    asimpl.
    replace (m1.[n.[ren ξ] .: ren ξ])
      with m1.[n/].[ren ξ] by autosubst.
    have[h|[r[A[B[s e]]]]]:=decide_act m1.[n/] ξ; subst.
    left. exists m1.[n/]; eauto.
    right. exists r. exists A. exists B. exists s.
    rewrite e; asimpl; eauto. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H2; subst.
    left. exists (App Z1 n).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (App (Act r1 A1 B1 s1) n).
    split; asimpl; eauto.
    intros; intro. inv H. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn _ _ H2; subst.
    left. exists (App m Z1).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (App m (Act r1 A1 B1 s1)).
    split; asimpl; eauto.
    intros; intro. inv H. }
  move=>A ihA m ihm Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihA _ _ H2; subst.
    left. exists (Fix Z1 m).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (Fix (Act r1 A1 B1 s1) m).
    split; asimpl; eauto.
    intros; intro. inv H. }
  { asimpl in H2.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H2; subst.
    left. exists (Fix A Z1).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (Fix A (Act r1 A1 B1 s1)).
    split; asimpl; eauto.
    intros; intro. inv H. }
  { asimpl.
    replace (m.[Fix A.[ren ξ] m.[ren (upren ξ)] .: ren ξ])
      with m.[Fix A m/].[ren ξ] by autosubst.
    have[h|[r1[A1[B1[s1 e]]]]]:=decide_act m.[Fix A m/] ξ.
    left. exists m.[Fix A m/]. eauto.
    right. exists r1. exists A1. exists B1. exists s1.
    rewrite e; asimpl. eauto. }
  move=>A ihA B ihB s r t Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihA _ _ H5; subst.
    left. exists (Sigma Z1 B s r t).
    split; eauto.
    intros; intro. inv H.
    left. exists (Sigma (Act r1 A1 B1 s1) B s r t).
    split; eauto.
    intros; intro. inv H. }
  { asimpl in H5.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihB _ _ H5; subst.
    left. exists (Sigma A Z1 s r t).
    split; asimpl; eauto.
    intros. intro. inv H.
    left. exists (Sigma A (Act r1 A1 B1 s1) s r t).
    split; asimpl; eauto.
    intros; intro. inv H. }
  move=>m ihm n ihn t Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H3; subst.
    left. exists (Pair Z1 n t).
    split; eauto.
    intros; intro. inv H.
    left. exists (Pair (Act r1 A1 B1 s1) n t).
    split; eauto.
    intros; intro. inv H. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn _ _ H3; subst.
    left. exists (Pair m Z1 t).
    split; asimpl; eauto.
    intros. intro. inv H.
    left. exists (Pair m (Act r1 A1 B1 s1) t).
    split; asimpl; eauto.
    intros; intro. inv H. }
  move=>m ihm n1 ihn1 n2 ihn2 Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H3; subst.
    left. exists (Case Z1 n1 n2).
    split; eauto.
    intros; intro. inv H.
    left. exists (Case (Act r1 A1 B1 s1) n1 n2).
    split; eauto.
    intros; intro. inv H. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn1 _ _ H3; subst.
    left. exists (Case m Z1 n2).
    split; eauto.
    intros; intro. inv H.
    left. exists (Case m (Act r1 A1 B1 s1) n2).
    split; eauto.
    intros; intro. inv H. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn2 _ _ H3; subst.
    left. exists (Case m n1 Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Case m n1 (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  { destruct m; inv H0.
    have[h|[r[A[B[s e]]]]]:=(decide_act n1.[ren ξ] id).
    left. exists n1. asimpl in h. eauto.
    destruct n1; inv e.
    right. exists r. exists n1. exists B0. exists s. eauto. }
  { destruct m; inv H0.
    have[h|[r[A[B[s e]]]]]:=(decide_act n2.[ren ξ] id).
    left. exists n2. asimpl in h. eauto.
    destruct n2; inv e.
    right. exists r. exists n2. exists B0. exists s. eauto. }
  move=>m ihm n ihn Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H2; subst.
    left. exists (LetIn1 Z1 n).
    split; eauto.
    intros; intro. inv H.
    left. exists (LetIn1 (Act r1 A1 B1 s1) n).
    split; eauto.
    intros; intro. inv H. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn _ _ H2; subst.
    left. exists (LetIn1 m Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (LetIn1 m (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  { destruct m; inv H0.
    have[h|[r[A[B[s e]]]]]:=(decide_act n.[ren ξ] id).
    left. exists n. asimpl in h. eauto.
    destruct n; inv e.
    right. exists r. exists n. exists B0. exists s. eauto. }
  move=>m ihm n ihn Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H2; subst.
    left. exists (LetIn2 Z1 n).
    split; eauto.
    intros; intro. inv H.
    left. exists (LetIn2 (Act r1 A1 B1 s1) n).
    split; eauto.
    intros; intro. inv H. }
  { replace n.[upn 2 (ren ξ)]
      with n.[ren (upren (upren ξ))] in H2 by autosubst.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn _ _ H2; subst.
    left. exists (LetIn2 m Z1).
    split; asimpl; eauto.
    intros; intro. inv H.
    left. exists (LetIn2 m (Act r1 A1 B1 s1)).
    split; asimpl; eauto.
    intros; intro. inv H. }
  { destruct m; inv H0.
    asimpl.
    replace (n.[m4.[ren ξ] .: m3.[ren ξ] .: ren ξ])
      with n.[m4,m3/].[ren ξ] by autosubst.
    have[h|[r[A[B[s e]]]]]:=(decide_act n.[m4,m3/] ξ).
    left. exists n.[m4,m3/]. eauto.
    right. exists r. exists A. exists B. exists s.
    rewrite e. asimpl; eauto. }
  move=>r A ihA B ihB s Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihA _ _ H4; subst.
    right. exists r. exists Z1. exists B. exists s.
    asimpl; eauto.
    right. exists r. exists (Act r1 A1 B1 s1). exists B. exists s.
    asimpl; eauto. }
  { asimpl in H4.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihB _ _ H4; subst.
    right. exists r. exists A. exists Z1. exists s.
    asimpl; eauto.
    right. exists r. exists A. exists (Act r1 A1 B1 s1). exists s.
    asimpl; eauto. }
  move=>r A ihA Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihA _ _ H2; subst.
    left. exists (Ch r Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Ch r (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  move=>m ihm n ihn Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihm _ _ H2; subst.
    left. exists (Fork Z1 n).
    split; eauto.
    intros; intro. inv H.
    left. exists (Fork (Act r1 A1 B1 s1) n).
    split; eauto.
    intros; intro. inv H. }
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihn _ _ H2; subst.
    left. exists (Fork m Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Fork m (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  move=>ch ihc Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihc _ _ H0; subst.
    left. exists (Recv Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Recv (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  move=>ch ihc Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihc _ _ H0; subst.
    left. exists (Send Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Send (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  move=>ch ihc Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihc _ _ H0; subst.
    left. exists (Close Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Close (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
  move=>ch ihc Y ξ st. inv st.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=ihc _ _ H0; subst.
    left. exists (Wait Z1).
    split; eauto.
    intros; intro. inv H.
    left. exists (Wait (Act r1 A1 B1 s1)).
    split; eauto.
    intros; intro. inv H. }
Qed.

Lemma dual_red X Y ξ :
  X.[ren ξ] ~>* Y ->
  (exists Z, Y = Z.[ren ξ] /\
    forall r A B s, ~Y = Act r A B s) \/
  (exists r A B s,
    Y = (Act r A B s).[ren ξ]).
Proof.
  move e:(X.[ren ξ])=>n rd.
  elim: rd e.
  move=>e; subst.
  destruct X.
  all: try solve[match goal with
  | [ |- (exists _, (?n).[ren _] = _ /\ _ ) \/ _ ] =>
    left; exists n;
    split; eauto;
    intros; asimpl=>H; inv H
  end].
  right.
  exists r. exists X. exists B. exists s. eauto.
  move=>y z rd ih st e; subst.
  have[[Z[e h]]|[r[A[B[s e]]]]]:=ih erefl; subst.
  { have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=dual_step st; subst.
    left. exists Z1; eauto.
    right. exists r1. exists A1. exists B1. exists s1. eauto. }
  { right.
    asimpl in st. inv st.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=dual_step H4; subst.
    exists r. exists Z1. exists B. exists s. asimpl; eauto.
    exists r. exists (Act r1 A1 B1 s1). exists B. exists s. asimpl; eauto.
    have[[Z1[e h1]]|[r1[A1[B1[s1 e]]]]]:=dual_step H4; subst.
    exists r. exists A. exists Z1. exists s. asimpl; eauto.
    exists r. exists A. exists (Act r1 A1 B1 s1). exists s. asimpl; eauto. }
Qed.

Lemma dual_conv Γ X r A B C s ξ :
  ok Γ ->
  X.[ren ξ] === Act r A B s ->
  Γ ⊢ X : C ->
  can_cancel ξ ->
  exists A' B',
    Γ ⊢ Act r A' B' s : C /\
    (Act r A' B' s).[ren ξ] === X.[ren ξ] /\
    (Act r A' B' s).[ren ξ] === Act r A B s.
Proof.
  move=>wf/church_rosser[x r1 r2] ty cc.
  have[A'[B'[rA[rB e]]]]:=red_act_inv r2; subst.
  have[[Z[e h]]|[r3[A3[B3[s3 e]]]]]:=dual_red r1; subst.
  exfalso.
  apply: h; eauto.
  asimpl in e. inv e.
  replace (Act r3 A3.[ren ξ] B3.[ren (upren ξ)] s3)
    with (Act r3 A3 B3 s3).[ren ξ] in r1 by autosubst.
  have:=red_ren_inv r1 cc.
  exists A3. exists B3.
  repeat split; asimpl.
  apply: subject_reduction; eauto.
  apply: conv_sym.
  apply: star_conv; eauto.
  asimpl in r1; eauto.
  apply: conv_sym.
  apply: star_conv; eauto.
Qed.
