open Bindlib
open Terms
open Norm

let rec aeq t1 t2 =
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Type, Type -> true
  | Prod (q1, t1, b1), Prod (q2, t2, b2) ->
    q1 = q2 &&
    aeq t1 t2 &&
    eq_binder aeq b1 b2
  | Lambda (q1, t1, b1), Lambda (q2, t2, b2) ->
    q1 = q2 &&
    aeq t1 t2 &&
    eq_binder aeq b1 b2
  | Fix (q1, t1, b1), Fix (q2, t2, b2) ->
    q1 = q2 &&
    aeq t1 t2 &&
    eq_binder aeq b1 b2
  | App (t11, t12), App (t21, t22) ->
    aeq t11 t21 &&
    aeq t12 t22
  | Magic, _ -> true
  | _, Magic -> true
  | _ -> false

let rec equal t1 t2 =
  if aeq t1 t2 then true
  else 
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    equal_term t1 t2

and equal_term t1 t2 =
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Type, Type -> true
  | Prod (q1, t1, b1), Prod (q2, t2, b2) ->
    q1 = q2 &&
    equal t1 t2 &&
    eq_binder equal b1 b2
  | Lambda (q1, t1, b1), Lambda (q2, t2, b2) ->
    q1 = q2 &&
    equal t1 t2 &&
    eq_binder equal b1 b2
  | Fix (q1, t1, b1), Fix (q2, t2, b2) ->
    q1 = q2 &&
    equal t1 t2 &&
    eq_binder equal b1 b2
  | App (t11, t12), App (t21, t22) ->
    equal t11 t21 &&
    equal t12 t22
  | Magic, _ -> true
  | _, Magic -> true
  | _ -> false
