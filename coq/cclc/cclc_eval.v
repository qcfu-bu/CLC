From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS clc_context clc_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value : term -> Prop :=
| value_var x : value (Var x)
| value_lam A m s t : value (Lam A m s t)
| value_it : value It
| value_pair m n s : 
  value m ->
  value n ->
  value (Pair m n s)
| value_send m :
  value m ->
  value (Send m).

Inductive eval_context :=
| EHole : eval_context
| EVar : var -> eval_context
| EAppL : eval_context -> term -> eval_context
| EAppR m : value m -> eval_context -> eval_context
| EPairL : eval_context -> term -> sort -> eval_context
| EPairR m : value m -> eval_context -> sort -> eval_context
| ELetIn1 : eval_context -> term -> eval_context
| ELetIn2 : eval_context -> term -> eval_context
| ESend : eval_context -> eval_context
| ERecv : eval_context -> eval_context
| EClose : eval_context -> eval_context
| EWait : eval_context -> eval_context.

Declare Scope eval_scope.
Delimit Scope eval_scope with C.
Bind Scope eval_scope with eval_context.
Local Open Scope eval_scope.

Fixpoint plug (e : eval_context) (t : term) : term :=
  match e with
  | EHole => t
  | EVar x => Var x
  | EAppL e m => App (plug e t) m
  | EAppR m _ e => App m (plug e t)
  | EPairL e m s => Pair (plug e t) m s
  | EPairR m _ e s => Pair m (plug e t) s
  | ELetIn1 e m => LetIn1 (plug e t) m
  | ELetIn2 e m => LetIn2 (plug e t) m
  | ESend e => Send (plug e t)
  | ERecv e => Recv (plug e t)
  | EClose e => Close (plug e t)
  | EWait e => Wait (plug e t)
  end.

Notation "c .[ m ] " := (plug c m)
  (at level 2, m at level 200, left associativity,
    format "c .[ m ]") : eval_scope.