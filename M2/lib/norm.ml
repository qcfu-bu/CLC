open Bindlib
open Terms

let rec cbv t =
  match t with
  | Var _ -> t
  | Type -> t
  | Prod (q, t, b) ->
    let t = cbv t in
    let x, b = unbind b in
    let b = cbv b in
    let b = unbox (bind_var x (lift b)) in
    Prod (q, t, b)
  | Lambda (q, t, b) ->
    let t = cbv t in
    let x, b = unbind b in
    let b = cbv b in
    let b = unbox (bind_var x (lift b)) in
    Lambda (q, t, b)
  | Fix (q, t, b) ->
    let t = cbv t in
    let x, b = unbind b in
    let b = cbv b in
    let b = unbox (bind_var x (lift b)) in
    Fix (q, t, b)
  | App (t1, t2) -> (
    match t1 with
    | Fix (_, _, b) ->
      let t1 = subst b t1 in
      cbv (App (t1, t2))
    | Lambda (_, _, b) -> 
      let t2 = cbv t2 in
      cbv (subst b t2)
    | _ -> App (t1, t2))
  | Magic -> t

let rec cbn t =
  match t with
  | Var _ -> t
  | Type -> t
  | Prod (q, t, b) ->
    let t = cbn t in
    let x, b = unbind b in
    let b = cbn b in
    let b = unbox (bind_var x (lift b)) in
    Prod (q, t, b)
  | Lambda (q, t, b) ->
    let t = cbn t in
    let x, b = unbind b in
    let b = cbn b in
    let b = unbox (bind_var x (lift b)) in
    Lambda (q, t, b)
  | Fix (q, t, b) ->
    let t = cbn t in
    let x, b = unbind b in
    let b = cbn b in
    let b = unbox (bind_var x (lift b)) in
    Fix (q, t, b)
  | App (t1, t2) -> (
    match t1 with
    | Fix (_, _, b) ->
      let t1 = subst b t1 in
      cbn (App (t1, t2))
    | Lambda (_, _, b) -> 
      cbn (subst b t2)
    | _ -> App (t1, t2))
  | Magic -> t

let rec whnf t = 
  match t with
  | Var _ -> t
  | Type -> t
  | Prod _ -> t
  | Lambda _ -> t
  | Fix _ -> t
  | App (t1, t2) -> (
    let t1 = whnf t1 in
    match t1 with
    | Fix (_, _, b) ->
      let t1 = subst b t1 in
      whnf (App (t1, t2))
    | Lambda (_, _, b) -> 
      let t2 = whnf t2 in
      whnf (subst b t2)
    | _ -> App (t1, t2))
  | Magic -> t
