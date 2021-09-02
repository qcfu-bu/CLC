open Bindlib
open Names
open Terms

let rec spine = function
  | App (t1, t2) ->
    let h, sp = spine t1 in
    (h, sp @ [t2])
  | h -> (h, [])

let rec aeq t1 t2 =
  match t1, t2 with
  | V x1, V x2 -> eq_vars x1 x2
  | L x1, L x2 -> eq_vars x1 x2
  | R x1, R x2 -> eq_vars x1 x2
  | M m1, M m2 -> M.equal m1 m2
  | Type, Type -> true
  | Prod (ty1, b1), Prod (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | Lambda b1, Lambda b2 ->
    eq_binder aeq b1 b2
  | App (t11, t12), App (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | _ -> false

let rec whnf t =
  match t with
  | V _ -> t
  | L _ -> t
  | R _ -> t
  | M x -> (
    match M.get x with
    | Some t -> whnf t
    | None -> t)
  | Type -> t
  | Prod _ -> t
  | Lambda _ -> t
  | App (t1, t2) -> (
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Lambda b, _ -> hsubst b t2
    | _ -> App (t1, t2))

and hsubst b t = whnf (subst b t)
  
let rec equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | V x1, V x2 -> eq_vars x1 x2
    | L x1, L x2 -> eq_vars x1 x2
    | R x1, R x2 -> eq_vars x1 x2
    | M m1, M m2 -> M.equal m1 m2 
    | Type, Type -> true
    | Prod (ty1, b1), Prod (ty2, b2) ->
      equal ty1 ty2 && eq_binder equal b1 b2
    | Lambda b1, Lambda b2 ->
      eq_binder equal b1 b2
    | App (t11, t12), App (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | _ -> false

