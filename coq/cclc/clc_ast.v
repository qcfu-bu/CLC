From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
(* core *)
| Var    (x : var)
| Sort   (s : sort) (l : nat)
| Pi     (A : term) (B : {bind term}) (s r t : sort)
| Lam    (A : term) (m : {bind term}) (s t : sort)
| App    (m n : term)
(* data *)
| Unit
| It
| Either
| Left
| Right
| Sigma  (A : term) (B : {bind term}) (s r t : sort)
| Pair   (m n : term) (t : sort)
| Case   (m n1 n2 : term)
| LetIn1 (m n : term)
| LetIn2 (m : term) (n : {bind 2 of term})
(* session *)
| Main
| Proto  (l : nat)
| InpEnd
| OutEnd
| Inp    (A : term) (B : {bind term}) (s : sort)
| Out    (A : term) (B : {bind term}) (s : sort)
| Ch     (A : term)
| Fork   (m n : term)
| Recv   (ch : term)
| Send   (ch : term)
| Close  (ch : term)
| Wait   (ch : term).

Notation "s @ l" := (Sort s l) (at level 30).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_beta A m n s t :
  (App (Lam A m s t) n) ~> m.[n/]
| step_lamL A A' m s t :
  A ~> A' ->
  Lam A m s t ~> Lam A' m s t
| step_lamR A m m' s t :
  m ~> m' ->
  Lam A m s t ~> Lam A m' s t
| step_piL A A' B s r t :
  A ~> A' ->
  Pi A B s r t ~> Pi A' B s r t
| step_piR A B B' s r t :
  B ~> B' ->
  Pi A B s r t ~> Pi A B' s r t
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| step_sigmaL A A' B s r t :
  A ~> A' ->
  Sigma A B s r t ~> Sigma A' B s r t
| step_sigmaR A B B' s r t :
  B ~> B' ->
  Sigma A B s r t ~> Sigma A B' s r t
| step_pairL m m' n t :
  m ~> m' ->
  Pair m n t ~> Pair m' n t
| step_pairR m n n' t :
  n ~> n' ->
  Pair m n t ~> Pair m n' t
| step_caseL m m' n1 n2 :
  m ~> m' ->
  Case m n1 n2 ~> Case m' n1 n2
| step_caseR1 m n1 n1' n2 :
  n1 ~> n1' ->
  Case m n1 n2 ~> Case m n1' n2
| step_caseR2 m n1 n2 n2' :
  n2 ~> n2' ->
  Case m n1 n2 ~> Case m n1 n2'
| step_iotaL n1 n2 :
  Case Left n1 n2 ~> n1
| step_iotaR n1 n2 :
  Case Right n1 n2 ~> n2
| step_letin1L m m' n :
  m ~> m' ->
  LetIn1 m n ~> LetIn1 m' n
| step_letin1R m n n' :
  n ~> n' ->
  LetIn1 m n ~> LetIn1 m n'
| step_iota1 n :
  LetIn1 It n ~> n
| step_letin2L m m' n :
  m ~> m' ->
  LetIn2 m n ~> LetIn2 m' n
| step_letin2R m n n' :
  n ~> n' ->
  LetIn2 m n ~> LetIn2 m n'
| step_iota2 m1 m2 n t :
  LetIn2 (Pair m1 m2 t) n ~> n.[m2,m1/]
| step_inpL A A' B s :
  A ~> A' ->
  Inp A B s ~> Inp A' B s
| step_inpR A B B' s :
  B ~> B' ->
  Inp A B s ~> Inp A B' s
| step_outL A A' B s :
  A ~> A' ->
  Out A B s ~> Out A' B s
| step_outR A B B' s :
  B ~> B' ->
  Out A B s ~> Out A B' s
| step_ch A A' :
  A ~> A' ->
  Ch A ~> Ch A'
| step_forkL m m' n :
  m ~> m' ->
  Fork m n ~> Fork m' n
| step_forkR m n n' :
  n ~> n' ->
  Fork m n ~> Fork m n'
| step_recv ch ch' :
  ch ~> ch' ->
  Recv ch ~> Recv ch'
| step_send ch ch' :
  ch ~> ch' ->
  Send ch ~> Send ch'
| step_close ch ch' :
  ch ~> ch' ->
  Close ch ~> Close ch'
| step_wait ch ch' :
  ch ~> ch' ->
  Wait ch ~> Wait ch'
where "m ~> n" := (step m n).

Notation red := (star step).
Notation "m ~>* n" := (red m n) (at level 30).
Notation "m === n" := (conv step m n) (at level 50).
