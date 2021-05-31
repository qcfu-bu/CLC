open Bindlib
open Rig
open Terms
open Norm

let rec aeq t1 t2 = 
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Ann (s1, t1), Ann (s2, t2) ->
    aeq s1 s2 && aeq t1 t2
  | Type, Type -> true
  | Prod (q1, t1, b1), Prod (q2, t2, b2) ->
    q1 = q2 &&
    aeq t1 t2 &&
    eq_binder aeq b1 b2
  | Lambda b1, Lambda b2 ->
    eq_binder aeq b1 b2
  | Fix b1, Fix b2 ->
    eq_binder aeq b1 b2
  | App (s1, t1), App (s2, t2) ->
    aeq s1 s2 && aeq t1 t2
  | _ -> false

let rec equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Var x1, Var x2 -> eq_vars x1 x2
    | Type, Type -> true
    | Prod (q1, t1, b1), Prod (q2, t2, b2) ->
      q1 = q2 &&
      equal t1 t2 &&
      eq_binder equal b1 b2
    | Lambda b1, Lambda b2 ->
      eq_binder equal b1 b2
    | Fix b1, Fix b2 ->
      eq_binder equal b1 b2
    | App (s1, t1), App (s2, t2) ->
      equal s1 s2 && equal t1 t2
    | _ -> false
