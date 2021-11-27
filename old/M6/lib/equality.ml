open Bindlib
open Terms

let rec aeq t1 t2 = 
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Ann (t1, ty1), Ann (t2, ty2) -> 
    aeq t1 t2 && aeq ty1 ty2
  | Type, Type -> true
  | Linear, Linear -> true
  | TyProd (ty1, b1), TyProd (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | LnProd (ty1, b1), LnProd (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | Lambda b1, Lambda b2 ->
    eq_binder aeq b1 b2
  | App (t11, t12), App (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | LetIn (t1, b1), LetIn (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Eq (t11, t12, ty1), Eq (t21, t22, ty2) ->
    aeq t11 t21 && aeq t12 t22 && aeq ty1 ty2
  | Refl (t1, ty1), Refl (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Ind (p1, pf1, t11, t12, eq1, ty1), Ind (p2, pf2, t21, t22, eq2, ty2) ->
    aeq p1 p2 && aeq pf1 pf2 && aeq t11 t21 && aeq t12 t22 && 
    aeq eq1 eq2 && aeq ty1 ty2
  | Tensor (ty1, b1), Tensor (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | Pair (t11, t12), Pair (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | LetPair (t1, mb1), LetPair (t2, mb2) ->
    aeq t1 t2 && eq_mbinder aeq mb1 mb2
  | CoProd (ty11, ty12), CoProd (ty21, ty22) ->
    aeq ty11 ty21 && aeq ty12 ty22
  | InjL t1, InjL t2 -> aeq t1 t2
  | InjR t1, InjR t2 -> aeq t1 t2
  | Case (t1, b11, b12), Case (t2, b21, b22) ->
    aeq t1 t2 && eq_binder aeq b11 b21 && eq_binder aeq b12 b22
  | Unit, Unit -> true
  | U, U -> true
  | Nat, Nat -> true
  | Zero, Zero -> true
  | Succ t1, Succ t2 -> aeq t1 t2
  | Iter (ty1, t11, t12, t13), Iter (ty2, t21, t22, t23) ->
    aeq ty1 ty2 && aeq t11 t21 && aeq t12 t22 && aeq t13 t23
  | PtsTo (t1, ty1), PtsTo (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Alloc, Alloc -> true
  | Free, Free -> true
  | Get, Get -> true
  | Set, Set -> true
  | _ -> false

let rec whnf t =
  match t with
  | Var _ -> t
  | Ann (t, _) -> whnf t
  | Type -> t
  | Linear -> t
  | TyProd _ -> t
  | LnProd _ -> t
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
  | Ind (p, pf, t1, t2, eq, ty) -> (
    let p = whnf p in
    let pf = whnf pf in
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    let eq = whnf eq in
    let ty = whnf ty in
    match eq with
    | Refl (t3, eq_ty) ->
      if (equal t1 t3 && equal t2 t3 && equal ty eq_ty)
      then whnf (App (pf, t3))
      else Ind (p, pf, t1, t2, eq, ty)
    | _ -> Ind (p, pf, t1, t2, eq, ty))
  | Tensor _ -> t
  | Pair _ -> t
  | LetPair (t, mb) -> (
    let t = whnf t in
    match t with
    | Pair (t1, t2) ->
      whnf (msubst mb [| t1; t2 |])
    | _ -> 
      let occurs = mbinder_occurs mb in
      if Array.for_all (fun x -> not x) occurs then
        whnf (snd (unmbind mb))
      else LetPair (t, mb))
  | CoProd _ -> t
  | InjL _ -> t
  | InjR _ -> t
  | Case (t, b1, b2) -> (
    let t = whnf t in
    match t with
    | InjL t -> whnf (subst b1 t)
    | InjR t -> whnf (subst b2 t)
    | _ -> Case (t, b1, b2))
  | Unit -> t
  | U -> t
  | Nat -> t
  | Zero -> t
  | Succ _ -> t
  | Iter (p, t1, t2, n) -> (
    let p = whnf p in
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    let n = whnf n in
    match n with
    | Zero -> whnf t1
    | Succ n ->
      whnf (App (App (t2, n), Iter (p, t1, t2, n)))
    | _ -> Iter (p, t1, t2, n))
  | PtsTo _ -> t
  | Alloc -> t
  | Free -> t
  | Get -> t
  | Set -> t

and equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Var x1, Var x2 -> eq_vars x1 x2
    | Ann (t1, ty1), Ann (t2, ty2) -> 
      equal t1 t2 && equal ty1 ty2
    | Type, Type -> true
    | Linear, Linear -> true
    | TyProd (ty1, b1), TyProd (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | LnProd (ty1, b1), LnProd (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | Lambda b1, Lambda b2 ->
      eq_binder equal b1 b2
    | App (t11, t12), App (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | LetIn (t1, b1), LetIn (t2, b2) ->
      equal t1 t2 && eq_binder equal b1 b2
    | Eq (t11, t12, ty1), Eq (t21, t22, ty2) ->
      equal t11 t21 && equal t12 t22 && equal ty1 ty2
    | Refl (t1, ty1), Refl (t2, ty2) ->
      equal t1 t2 && equal ty1 ty2
    | Ind (p1, pf1, t11, t12, eq1, ty1), Ind (p2, pf2, t21, t22, eq2, ty2) ->
      equal p1 p2 && equal pf1 pf2 && equal t11 t21 && equal t12 t22 && 
      equal eq1 eq2 && equal ty1 ty2
    | Tensor (ty1, b1), Tensor (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | Pair (t11, t12), Pair (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | LetPair (t1, mb1), LetPair (t2, mb2) ->
      equal t1 t2 && eq_mbinder equal mb1 mb2
    | CoProd (ty11, ty12), CoProd (ty21, ty22) ->
      equal ty11 ty21 && equal ty12 ty22
    | InjL t1, InjL t2 -> equal t1 t2
    | InjR t1, InjR t2 -> equal t1 t2
    | Case (t1, b11, b12), Case (t2, b21, b22) ->
      equal t1 t2 && eq_binder equal b11 b21 && eq_binder equal b12 b22
    | Unit, Unit -> true
    | U, U -> true
    | Nat, Nat -> true
    | Zero, Zero -> true
    | Succ t1, Succ t2 -> equal t1 t2
    | Iter (ty1, t11, t12, t13), Iter (ty2, t21, t22, t23) ->
      equal ty1 ty2 && equal t11 t21 && equal t12 t22 && equal t13 t23
    | PtsTo (t1, ty1), PtsTo (t2, ty2) ->
      equal t1 t2 && equal ty1 ty2
    | Alloc, Alloc -> true
    | Free, Free -> true
    | Get, Get -> true
    | Set, Set -> true
    | _ -> false
