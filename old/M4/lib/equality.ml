open Bindlib
open Terms

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
  | LetIn (t1, b1), LetIn (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Eq (t11, t12, ty1), Eq (t21, t22, ty2) ->
    aeq t11 t21 && aeq t12 t22 && aeq ty1 ty2
  | Refl (t1, ty1), Refl (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Ind (p1, pf1, t11, t12, eq1), Ind (p2, pf2, t21, t22, eq2) ->
    aeq p1 p2 && aeq pf1 pf2 && aeq t11 t21 && aeq t12 t22 && 
    aeq eq1 eq2
  | Nat, Nat -> true
  | Zero, Zero -> true
  | Succ t1, Succ t2 -> aeq t1 t2
  | Nat_elim (p1, t11, t12, n1), Nat_elim (p2, t21, t22, n2) ->
    aeq p1 p2 && aeq t11 t21 && aeq t12 t22 && aeq n1 n2
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
  | Axiom (ty1, b1), Axiom (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | _ -> false

let rec whnf t = 
  match t with
  | Var _ -> t
  | Ann (t, _) -> whnf t
  | Type _ -> t
  | Prod _ -> t
  | Lolli _ -> t
  | Lambda _ -> t
  | App (t1, t2) -> (
    let t1 = whnf t1 in
    match t1 with
    | Lambda b ->
      let t2 = whnf t2 in
      whnf (subst b t2)
    | _ -> App (t1, t2))
  | LetIn (t, b) ->
    let t = whnf t in
    whnf (subst b t)
  | Eq _ -> t
  | Refl _ -> t
  | Ind (p, pf, t1, t2, eq) -> (
    let p = whnf p in
    let pf = whnf pf in
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    let eq = whnf eq in
    match eq with
    | Refl (t3, ty) ->
      if (equal t1 t3 && equal t2 t3)
      then whnf (App (pf, t3))
      else Ind (p, pf, t1, t2, Refl (t3, ty))
    | _ -> Ind (p, pf, t1, t2, eq))
  | Nat -> t
  | Zero -> t
  | Succ _ -> t
  | Nat_elim (p, t1, t2, n) -> (
    let p = whnf p in
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    let n = whnf n in
    match n with
    | Zero -> whnf t1
    | Succ n ->
      whnf (App (App (t2, n), Nat_elim (p, t1, t2, n)))
    | _ -> Nat_elim (p, t1, t2, n))
  | G _ -> t
  | G_intro t -> (
    let t = whnf t in
    match t with
    | G_elim t -> whnf t
    | _ -> G_intro t)
  | G_elim t -> (
    let t = whnf t in
    match t with
    | G_intro t -> whnf t
    | _ -> G_elim t)
  | F _ -> t
  | F_intro _ -> t
  | F_elim (t, mb) -> (
    let t = whnf t in
    match t with
    | F_intro (t1, t2) ->
      whnf (msubst mb [| t1; t2 |])
    | _ -> F_elim (t, mb))
  | Sum _ -> t
  | Tensor _ -> t
  | And _ -> t
  | Pair _ -> t
  | Proj1 t -> (
    let t = whnf t in
    match t with
    | Pair (t, _) -> whnf t
    | _ -> Proj1 t)
  | Proj2 t -> (
    let t = whnf t in
    match t with
    | Pair (_, t) -> whnf t
    | _ -> Proj1 t)
  | Tensor_elim (t, mb) -> (
    let t = whnf t in
    match t with
    | Pair (t1, t2) ->
      whnf (msubst mb [| t1; t2 |])
    | _ -> Tensor_elim (t, mb))
  | Unit _ -> t
  | True -> t
  | U -> t
  | Unit_elim (t1, t2) -> (
    let t1 = whnf t1 in
    match t1 with
    | U -> whnf t2
    | _ -> Unit_elim (t1, t2))
  | Axiom (ty, b) -> 
    let ty = whnf ty in
    Axiom (ty, b)

and equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Var x1, Var x2 -> eq_vars x1 x2
    | Ann (t1, ty1), Ann (t2, ty2) -> 
      equal t1 t2 && equal ty1 ty2
    | Type m1, Type m2 -> m1 = m2
    | Prod (ty1, b1), Prod (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | Lolli (ty11, ty12), Lolli (ty21, ty22) ->
      equal ty11 ty21 && equal ty12 ty22
    | Lambda b1, Lambda b2 -> eq_binder equal b1 b2
    | App (t11, t12), App (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | LetIn (t1, b1), LetIn (t2, b2) ->
      equal t1 t2 && eq_binder equal b1 b2
    | Eq (t11, t12, ty1), Eq (t21, t22, ty2) ->
      equal t11 t21 && equal t12 t22 && equal ty1 ty2
    | Refl (t1, ty1), Refl (t2, ty2) -> 
      equal t1 t2 && equal ty1 ty2
    | Ind (p1, pf1, t11, t12, eq1), Ind (p2, pf2, t21, t22, eq2) ->
      equal p1 p2 && equal pf1 pf2 && equal t11 t21 && equal t12 t22 &&
      equal eq1 eq2
    | Nat, Nat -> true
    | Zero, Zero -> true
    | Succ t1, Succ t2 -> equal t1 t2
    | Nat_elim (p1, t11, t12, n1), Nat_elim (p2, t21, t22, n2) ->
      equal p1 p2 && equal t11 t21 && equal t12 t22 && aeq n1 n2
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
    | Axiom (ty1, b1), Axiom (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | _ -> false
