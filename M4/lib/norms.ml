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
  | LetIn (t, b) ->
    let t = whnf t in
    whnf (subst b t)
  | Eq _ -> t
  | Refl _ -> t
  | Ind _ -> t
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

let rec nf t = 
  match t with
  | Var _ -> t
  | Ann (t, _) -> nf t
  | Type _ -> t
  | Prod (ty, b) -> 
    let x, b = unbind b in
    let ty = nf ty in
    let b = unbox (bind_var x (lift (nf b))) in
    Prod (ty, b)
  | Lolli (ty1, ty2) -> 
    let ty1 = nf ty1 in
    let ty2 = nf ty2 in
    Lolli (ty1, ty2)
  | Lambda b -> 
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    Lambda b
  | App (t1, t2) -> (
    let t1 = nf t1 in
    let t2 = nf t2 in
    match t1 with
    | Lambda b ->
      nf (subst b t2)
    | _ -> App (t1, t2))
  | LetIn (t, b) ->
    let t = nf t in
    nf (subst b t)
  | Eq (t1, t2, ty) ->
    Eq (nf t1, nf t2, nf ty)
  | Refl t -> Refl (nf t)
  | Ind (p, pf, t1, t2, eq) ->
    Ind (nf p, nf pf, nf t1, nf t2, nf eq)
  | G t -> G (nf t)
  | G_intro t -> (
    let t = nf t in
    match t with
    | G_elim t -> nf t
    | _ -> G_intro t)
  | G_elim t -> (
    let t = nf t in
    match t with
    | G_intro t -> nf t
    | _ -> G_elim t)
  | F (ty, b) -> 
    let x, b = unbind b in
    let ty = nf ty in
    let b = unbox (bind_var x (lift (nf b))) in
    F (ty, b)
  | F_intro (t1, t2) ->
    F_intro (nf t1, nf t2)
  | F_elim (t, mb) -> (
    let t = nf t in
    match t with
    | F_intro (t1, t2) ->
      nf (msubst mb [| t1; t2 |])
    | _ -> F_elim (t, mb))
  | Sum (ty, b) ->
    let x, b = unbind b in
    let ty = nf ty in
    let b = unbox (bind_var x (lift (nf b))) in
    Sum (ty, b)
  | Tensor (ty1, ty2) ->
    Tensor (nf ty1, nf ty2)
  | And (ty1, ty2) ->
    And (nf ty1, nf ty2)
  | Pair (t1, t2) ->
    Pair (nf t1, nf t2)
  | Proj1 t -> (
    let t = nf t in
    match t with
    | Pair (t, _) -> nf t
    | _ -> Proj1 t)
  | Proj2 t -> (
    let t = nf t in
    match t with
    | Pair (_, t) -> nf t
    | _ -> Proj1 t)
  | Tensor_elim (t, mb) -> (
    let t = nf t in
    match t with
    | Pair (t1, t2) ->
      nf (msubst mb [| t1; t2 |])
    | _ -> Tensor_elim (t, mb))
  | Unit _ -> t
  | True -> t
  | U -> t
  | Unit_elim (t1, t2) -> (
    let t1 = nf t1 in
    match t1 with
    | U -> nf t2
    | _ -> Unit_elim (t1, t2))
  | Axiom (ty, b) -> 
    let x, b = unbind b in
    let ty = nf ty in
    let b = unbox (bind_var x (lift (nf b))) in
    Axiom (ty, b)