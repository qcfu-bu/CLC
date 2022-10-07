From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export clc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value : term -> Prop :=
| value_var x : value (Var x)
| value_sort s : value (Sort s)
| value_pi A B s : value (Pi A B s)
| value_lam A m s : value (Lam A m s)
| value_fix A m : value (Fix A m)
| value_unit : value (Unit)
| value_it : value (It)
| value_either : value (Either)
| value_left : value (Left)
| value_right : value (Right)
| value_sigma A B s : value (Sigma A B s)
| value_pair m n t : value m -> value n -> value (Pair m n t)
| value_main : value (Main)
| value_proto : value (Proto)
| value_stop r : value (Stop r)
| value_act r A B : value (Act r A B)
| value_ch r A : value (Ch r A)
| value_recv m : value m -> value (Recv m)
| value_send m : value m -> value (Send m).

Reserved Notation "m ~> n" (at level 30).
Inductive step : term -> term -> Prop :=
| step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| step_beta A m v s :
  value v ->
  (App (Lam A m s) v) ~> m.[v/]
| step_rbeta A m :
  Fix A m ~> m.[Fix A m/]
| step_pairL m m' n t :
  m ~> m' ->
  Pair m n t ~> Pair m' n t
| step_pairR m n n' t :
  n ~> n' ->
  Pair m n t ~> Pair m n' t
| step_case m m' n1 n2 :
  m ~> m' ->
  Case m n1 n2 ~> Case m' n1 n2
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
  value (Pair m1 m2 t) ->
  LetIn2 (Pair m1 m2 t) n ~> n.[m2,m1/]
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
