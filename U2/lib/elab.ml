open Bindlib
open Names
open Terms
open Context

let rec elab ctx t ty =
  match t with
  | V x ->
    let _, m_app = Ctx.fresh ctx ty in
    let t_ty = Ctx.find ctx x in
    let eqn = Eqn (ctx, t, t_ty, m_app, ty) in
    (m_app, eqn :: [])
  | M x ->
    let _, m_app = Ctx.fresh ctx ty in
    let t_ty = M.ty x in
    let eqn = Eqn (ctx, t, t_ty, m_app, ty) in
    (m_app, eqn :: [])
  | Type ->
    let _, m_app = Ctx.fresh ctx ty in
    let eqn = Eqn (ctx, Type, Type, m_app, ty) in
    (m_app, eqn :: [])
  | Prod (a, b) ->
    let x, b = unbind b in
    let a', a_c = elab ctx a Type in
    let b', b_c = elab (Ctx.add1 ctx x a') b Type in
    let _, m_app = Ctx.fresh ctx ty in
    let t = unbox (_Prod (lift a') (bind_var x (lift b'))) in
    let eqn = Eqn (ctx, t, Type, m_app, ty) in
    (m_app, eqn :: a_c @ b_c)
  | Lambda b ->
    let x, ub = unbind b in
    let m1, m1_app = Ctx.fresh ctx Type in
    let ctx' = Ctx.add1 ctx x (M m1) in
    let _, m2_app = Ctx.fresh ctx' Type in
    let ub, c = elab ctx' ub m2_app in
    let _, m_app = Ctx.fresh ctx ty in
    let t = unbox (_Lambda (bind_var x (lift ub))) in
    let t_ty = Prod (m1_app, unbox (bind_var x (lift m2_app))) in
    let eqn = Eqn (ctx, t, t_ty, m_app, ty) in
    (m_app, eqn :: c)
  | App (t1, t2) ->
    let x = mk "x" in
    let m1, m1_app = Ctx.fresh ctx Type in
    let ctx' = Ctx.add1 ctx x (M m1) in
    let _, m2_app = Ctx.fresh ctx' Type in
    let t1_b = bind_var x (lift m2_app) in
    let t1_ty = unbox (_Prod (lift m1_app) t1_b) in
    let t1, t1_c = elab ctx t1 t1_ty in
    let t2, t2_c = elab ctx t2 m2_app in
    let _, m_app = Ctx.fresh ctx ty in
    let t = App (t1, t2) in
    let t_ty = subst (unbox t1_b) t2 in
    let eqn = Eqn (ctx, t, t_ty, m_app, ty) in
    (m_app, eqn :: t1_c @ t2_c)
  | _ -> failwith "elab forms"