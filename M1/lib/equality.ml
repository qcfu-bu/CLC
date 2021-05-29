open Names
open Constr

let rec aeq t1 t2 =
  match (t1, t2) with
  | Rel i, Rel j -> i = j
  | Var id1, Var id2 -> Id.equal id1 id2
  | Type, Type -> true
  | Prod (b1, t1), Prod (b2, t2) ->
      q_of b1 = q_of b2 && aeq (annot_of b1) (annot_of b2) && aeq t1 t2
  | Lambda (b1, t1), Lambda (b2, t2) ->
      q_of b1 = q_of b2 && aeq (annot_of b1) (annot_of b2) && aeq t1 t2
  | Fix (b1, t1), Fix (b2, t2) ->
      q_of b1 = q_of b2 && aeq (annot_of b1) (annot_of b2) && aeq t1 t2
  | App (t11, t12), App (t21, t22) -> aeq t11 t21 && aeq t12 t22
  | Magic, _ -> true
  | _, Magic -> true
  | _ -> false

let rec equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    equal_term t1 t2

and whnf t =
  match t with
  | Rel _ -> t
  | Var _ -> t
  | Type -> t
  | Prod _ -> t
  | Lambda _ -> t
  | Fix _ -> t
  | App (t1, t2) -> (
      let t1 = whnf t1 in
      let t2 = whnf t2 in
      match t1 with
      | Fix (b, t1) as f ->
          let t1 = unbind ~binder:b t1 in
          let t1 = subst ~binder:b ~s:f t1 in
          whnf (App (t1, t2))
      | Lambda (b, t1) ->
          let t1 = unbind ~binder:b t1 in
          let t1 = subst ~binder:b ~s:t2 t1 in
          whnf t1
      | _ -> App (t1, t2))
  | Magic -> t

and equal_term t1 t2 =
  match (t1, t2) with
  | Rel i, Rel j -> i = j
  | Var id1, Var id2 -> Id.equal id1 id2
  | Type, Type -> true
  | Prod (b1, t1), Prod (b2, t2) ->
      q_of b1 = q_of b2 && equal (annot_of b1) (annot_of b2) && equal t1 t2
  | Lambda (b1, t1), Lambda (b2, t2) ->
      q_of b1 = q_of b2 && equal (annot_of b1) (annot_of b2) && equal t1 t2
  | Fix (b1, t1), Fix (b2, t2) ->
      q_of b1 = q_of b2 && equal (annot_of b1) (annot_of b2) && equal t1 t2
  | App (t11, t12), App (t21, t22) -> equal t11 t21 && equal t12 t22
  | Magic, _ -> true
  | _, Magic -> true
  | _ -> false
