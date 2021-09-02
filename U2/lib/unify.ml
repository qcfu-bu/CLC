open Bindlib
open Terms
open Context
open Equality

let rec simpl eqn =
  let Eqn (ctx, t1, ty1, t2, ty2) = eqn in
  if equal ty1 ty2 && equal t1 t2 then None
  else
    let ctx = simpl_var ctx t1 ty1 t2 ty2 in
    let ctx = simpl_twin ctx t1 ty1 t2 ty2 in
    Some (Eqn (ctx, t1, ty1, t2, ty2))

and simpl_var ctx t1 ty1 t2 ty2 =
  match Ctx.pop ctx with
  | Some (e, ctx') -> (
    let x = 
      match e with
      | Single (x, _) -> x
      | Twin (x, _, _) -> x
    in
    if 
      not (occur x (lift t1)) &&
      not (occur x (lift t2)) &&
      not (occur x (lift ty1)) &&
      not (occur x (lift ty2))
    then
      simpl_var ctx' t1 ty1 t2 ty2
    else
      let ctx' = simpl_var ctx' t1 ty1 t2 ty2 in
      Ctx.add ctx' e)
  | None -> ctx

and simpl_twin ctx t1 ty1 t2 ty2 =
  match Ctx.pop ctx with
  | Some (e, ctx) -> (
    let opt = 
      match e with
      | Single _ -> None
      | Twin (x, ty1, ty2) ->
        if equal ty1 ty2
        then Some (x, ty1)
        else None
    in
    match opt with
    | Some (x, ty) ->
      let t1 = subst_free x t1 (V x) in
      let t2 = subst_free x t2 (V x) in
      let ty1 = subst_free x ty1 (V x) in
      let ty2 = subst_free x ty2 (V x) in
      let ctx = simpl_twin ctx t1 ty1 t2 ty2 in
      Ctx.add1 ctx x ty 
    | None ->
      let ctx = simpl_twin ctx t1 ty1 t2 ty2 in
      Ctx.add ctx e)
  | None -> ctx

let unify eqn =
  let Eqn (ctx, t1, ty1, t2, ty2) = eqn in
  