open Bindlib
open Terms
open Norms

let rec aeq t1 t2 =
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Ann (t1, ty1), Ann (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Type m1, Type m2 -> m1 = m2
  | Prod (ty1, b1), Prod (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | Lolli (ty11, ty12), Lolli (ty21, ty22) ->
    aeq ty11 ty21 && aeq ty12 ty22
  | Lambda b1, Lambda b2 -> eq_binder aeq b1 b2
  | App (t11, t12), App (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | Eq (t11, t12, ty1), Eq (t21, t22, ty2) ->
    aeq t11 t21 && aeq t12 t22 && aeq ty1 ty2
  | Refl t1, Refl t2 ->
    aeq t1 t2
  | Ind (p1, pf1, t11, t12, eq1), Ind (p2, pf2, t21, t22, eq2) ->
    aeq p1 p2 && aeq pf1 pf2 && 
    aeq t11 t21 && aeq t12 t22 && 
    aeq eq1 eq2
  | G ty1, G ty2 -> aeq ty1 ty2
  | G_intro t1, G_intro t2 -> aeq t1 t2
  | G_elim t1, G_elim t2 -> aeq t1 t2
  | F (ty1, b1), F (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | F_intro (t11, t12), F_intro (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | F_elim (t1, mb1), F_elim (t2, mb2) ->
    aeq t1 t2 && eq_mbinder aeq  mb1 mb2
  | Sum (ty1, b1), Sum (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | Tensor (ty11, ty12), Tensor (ty21, ty22) ->
    aeq ty11 ty21 && aeq ty12 ty22
  | And (ty11, ty12), And (ty21, ty22) ->
    aeq ty11 ty21 && aeq ty12 ty22
  | Pair (t11, t12), Pair (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | Proj1 t1, Proj1 t2 -> aeq t1 t2
  | Proj2 t1, Proj2 t2 -> aeq t1 t2
  | Tensor_elim (t1, mb1), Tensor_elim (t2, mb2) ->
    aeq t1 t2 && eq_mbinder aeq mb1 mb2
  | Unit m1, Unit m2 -> m1 = m2
  | True, True -> true
  | U, U -> true
  | Unit_elim (t11, t12), Unit_elim (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | _ -> false

let rec equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Var x1, Var x2 -> eq_vars x1 x2
    | Ann (t1, _), _ -> equal t1 t2
    | _, Ann (t2, _) -> equal t1 t2
    | Type m1, Type m2 -> m1 = m2
    | Prod (ty1, b1), Prod (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | Lolli (ty11, ty12), Lolli (ty21, ty22) ->
      equal ty11 ty21 && equal ty12 ty22
    | Lambda b1, Lambda b2 -> eq_binder equal b1 b2
    | App (t11, t12), App (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | Eq (t11, t12, ty1), Eq (t21, t22, ty2) ->
      equal t11 t21 && equal t12 t22 && equal ty1 ty2
    | Refl t1, Refl t2 -> equal t1 t2
    | Ind (p1, pf1, t11, t12, eq1), _ -> (
      if equal t11 t12 && equal (Refl t11) eq1
      then equal (App (pf1, t11)) t2
      else
        match t2 with
        | Ind (p2, pf2, t21, t22, eq2) ->
          equal p1 p2 && equal pf1 pf2 &&
          equal t11 t21 && equal t12 t22 &&
          equal eq1 eq2
        | _ -> false)
    | _, Ind (p2, pf2, t21, t22, eq2) -> (
      if equal t21 t22 && equal (Refl t21) eq2
      then equal t1 (App (pf2, t21))
      else
        match t1 with
        | Ind (p1, pf1, t11, t12, eq1) ->
          equal p1 p2 && equal pf1 pf2 &&
          equal t11 t21 && equal t12 t22 &&
          equal eq1 eq2
        | _ -> false)
    | G ty1, G ty2 -> equal ty1 ty2
    | G_intro t1, G_intro t2 -> equal t1 t2
    | G_elim t1, G_elim t2 -> equal t1 t2
    | F (ty1, b1), F (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | F_intro (t11, t12), F_intro (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | F_elim (t1, mb1), F_elim (t2, mb2) ->
      equal t1 t2 && eq_mbinder equal  mb1 mb2
    | Sum (ty1, b1), Sum (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | Tensor (ty11, ty12), Tensor (ty21, ty22) ->
      equal ty11 ty21 && equal ty12 ty22
    | And (ty11, ty12), And (ty21, ty22) ->
      equal ty11 ty21 && equal ty12 ty22
    | Pair (t11, t12), Pair (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | Proj1 t1, Proj1 t2 -> equal t1 t2
    | Proj2 t1, Proj2 t2 -> equal t1 t2
    | Tensor_elim (t1, mb1), Tensor_elim (t2, mb2) ->
      equal t1 t2 && eq_mbinder equal mb1 mb2
    | Unit m1, Unit m2 -> m1 = m2
    | True, True -> true
    | U, U -> true
    | Unit_elim (t11, t12), Unit_elim (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | _ -> false
