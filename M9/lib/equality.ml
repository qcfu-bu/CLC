open Bindlib
open Names
open Terms

let rec aeq t1 t2 =
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Meta x1, Meta x2 -> Meta.equal x1 x2
  | Ann (t1, ty1), Ann (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Type, Type -> true
  | Linear, Linear -> true
  | TyProd (t1, b1), TyProd (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | LnProd (t1, b1), LnProd (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Lambda b1, Lambda b2 -> 
    eq_binder aeq b1 b2
  | Fix b1, Fix b2 -> 
    eq_binder aeq b1 b2
  | App (t11, t12), App (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | LetIn (t1, b1), LetIn (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | TCons (id1, ts1), TCons (id2, ts2) ->
    Id.equal id1 id2 && List.equal aeq ts1 ts2
  | DCons (id1, ts1), DCons (id2, ts2) ->
    Id.equal id1 id2 && List.equal aeq ts1 ts2
  | Match (t1, mot1, ps1), Match (t2, mot2, ps2) ->
    aeq t1 t2 &&
    Option.equal (eq_binder (eq_binder_p aeq)) mot1 mot2 &&
    List.equal (eq_binder_p aeq) ps1 ps2
  | Axiom (id1, ty1), Axiom (id2, ty2) ->
    Id.equal id1 id2 && aeq ty1 ty2
  | _ -> false

let rec whnf t =
  match t with
  | Var _ -> t
  | Meta x -> (
    match Meta.get x with
    | Some x -> whnf x
    | None -> t)
  | Ann (t, _) -> whnf t
  | Type -> t
  | Linear -> t
  | TyProd _ -> t
  | LnProd _ -> t
  | Lambda _ -> t
  | Fix _ -> t
  | App (t1, t2) -> (
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1 with
    | Lambda b -> whnf (subst b t2)
    | Fix b -> whnf (App (subst b t1, t2))
    | _ -> App (t1, t2))
  | LetIn (t, b) ->
    let t = whnf t in
    whnf (subst b t)
  | TCons _ -> t
  | DCons _ -> t
  | Match (t, m, ps) -> (
    let t = whnf t in
    let opt =
      List.fold_left
        (fun opt pb ->
          match opt with
          | Some _ -> opt
          | None ->
            try Some (subst_p pb t)
            with _ -> None)
        None ps
    in
    match opt with
    | Some t -> whnf t
    | None -> Match (t, m, ps))
  | Axiom _ -> t