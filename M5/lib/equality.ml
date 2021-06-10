open Bindlib
open Terms

let rec aeq t1 t2 = 
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Ann (s1, t1), Ann (s2, t2) ->
    aeq s1 s2 && aeq t1 t2
  | Type, Type -> true
  | Linear, Linear -> true
  | TyProd (t1, b1), TyProd (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | LnProd (t1, b1), LnProd (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Lambda b1, Lambda b2 ->
    eq_binder aeq b1 b2
  | App (s1, t1), App (s2, t2) ->
    aeq s1 s2 && aeq t1 t2
  | LetIn (t1, b1), LetIn (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Axiom (t1, b1), Axiom (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
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
  | App (s, t) -> (
    let s = whnf s in
    match s with
    | Lambda b ->
      let t = whnf t in
      whnf (subst b t)
    | _ -> App (s, whnf t))
  | LetIn (t, b) ->
    let t = whnf t in
    whnf (subst b t)
  | Axiom (t, b) ->
    let t = whnf t in
    let x, b = unbind b in
    let b = whnf b in
    let b = unbox (bind_var x (lift b)) in
    Axiom (t, b)

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
    | TyProd (t1, b1), TyProd (t2, b2) ->
      equal t1 t2 &&
      eq_binder equal b1 b2
    | LnProd (t1, b1), LnProd (t2, b2) ->
      equal t1 t2 &&
      eq_binder equal b1 b2
    | Lambda b1, Lambda b2 ->
      eq_binder equal b1 b2
    | App (s1, t1), App (s2, t2) ->
      equal s1 s2 && equal t1 t2
    | LetIn (t1, b1), LetIn (t2, b2) ->
      equal t1 t2 && eq_binder equal b1 b2
    | Axiom (t1, b1), Axiom (t2, b2) ->
      equal t1 t2 &&
      eq_binder equal b1 b2
    | _ -> false

