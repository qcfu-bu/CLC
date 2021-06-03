open Bindlib
open Terms

let rec whnf t = 
  match t with
  | Var _ -> t
  | Ann _ -> t
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