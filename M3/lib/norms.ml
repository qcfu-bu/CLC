open Bindlib
open Terms

let rec cbv t =
  match t with
  | Var _ -> t
  | Ann (s, _) -> cbv s
  | Type -> t
  | Prod (q, t, b) ->
    let t = cbv t in
    let x, b = unbind b in
    let b = cbv b in
    let b = unbox (bind_var x (lift b)) in
    Prod (q, t, b)
  | Lambda b ->
    let x, b = unbind b in
    let b = cbv b in
    let b = unbox (bind_var x (lift b)) in
    Lambda b
  | Fix b ->
    let x, b = unbind b in
    let b = cbv b in
    let b = unbox (bind_var x (lift b)) in
    Fix b
  | App (s, t) -> (
    let s = cbv s in
    match s with
    | Fix b ->
      let s = subst b s in
      cbv (App (s, t))
    | Lambda b ->
      let t = cbv t in
      cbv (subst b t)
    | _ -> App (s, cbv t))

let rec cbn t =
  match t with
  | Var _ -> t
  | Ann (s, _) -> cbn s
  | Type -> t
  | Prod (q, t, b) ->
    let t = cbn t in
    let x, b = unbind b in
    let b = cbn b in
    let b = unbox (bind_var x (lift b)) in
    Prod (q, t, b)
  | Lambda b ->
    let x, b = unbind b in
    let b = cbn b in
    let b = unbox (bind_var x (lift b)) in
    Lambda b
  | Fix b ->
    let x, b = unbind b in
    let b = cbn b in
    let b = unbox (bind_var x (lift b)) in
    Fix b
  | App (s, t) -> (
    let s = cbn s in
    match s with
    | Fix b ->
      let s = subst b s in
      cbn (App (s, t))
    | Lambda b ->
      cbn (subst b t)
    | _ -> App (s, cbn t))

let rec whnf t =
  match t with
  | Var _ -> t
  | Ann (s, _) -> whnf s
  | Type -> t
  | Prod _ -> t
  | Lambda _ -> t
  | Fix _ -> t
  | App (s, t) -> (
    let s = whnf s in
    match s with
    | Fix b ->
      let s = subst b s in
      whnf (App (s, t))
    | Lambda b ->
      let t = whnf t in
      whnf (subst b t)
    | _ -> App (s, whnf t))