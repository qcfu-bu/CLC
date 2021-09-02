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

let rec nf t =
  match t with
  | Var _ -> t
  | Meta x -> (
    match Meta.get x with
    | Some x -> nf x
    | None -> t)
  | Ann (t, _) -> nf t
  | Type -> t
  | Linear -> t
  | TyProd (t, b) ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    TyProd (nf t, b)
  | LnProd (t, b) ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    LnProd (nf t, b)
  | Lambda b ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    Lambda b
  | Fix b ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    Fix b
  | App (t1, t2) -> (
    let t1 = nf t1 in
    let t2 = nf t2 in
    match t1 with
    | Lambda b -> nf (subst b t2)
    | Fix b -> nf (App (subst b t1, t2))
    | _ -> App (t1, t2))
  | LetIn (t, b) ->
    let t = nf t in
    nf (subst b t)
  | TCons (id, ts) ->
    TCons (id, List.map nf ts)
  | DCons (id, ts) ->
    DCons (id, List.map nf ts)
  | Match (t, m, ps) -> (
    let t = nf t in
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
    | Some t -> nf t
    | None -> Match (t, m, ps))
  | Axiom (id, ty) -> Axiom (id, nf ty)

let rec occurs x t =
  match t with
  | Var _ -> false
  | Meta y -> (
    match Meta.get y with
    | Some t -> occurs x t
    | None -> Meta.equal x y)
  | Ann (t, ty) ->
    occurs x t || occurs x ty
  | Type -> false
  | Linear -> false
  | TyProd (t, b) ->
    let _, ub = unbind b in
    occurs x t || occurs x ub
  | LnProd (t, b) ->
    let _, ub = unbind b in
    occurs x t || occurs x ub
  | Lambda b ->
    let _, ub = unbind b in
    occurs x ub
  | Fix b ->
    let _, ub = unbind b in
    occurs x ub
  | App (t1, t2) ->
    occurs x t1 || occurs x t2
  | LetIn (t, b) ->
    let _, ub = unbind b in
    occurs x t || occurs x ub
  | TCons (_, ts) ->
    List.fold_left (fun acc t -> acc || occurs x t) false ts
  | DCons (_, ts) ->
    List.fold_left (fun acc t -> acc || occurs x t) false ts
  | Match (t, mot, pbs) -> (
    let ts = List.map (fun pb -> snd (unbind_p pb)) pbs in
    if occurs x t || List.fold_left (fun acc t -> acc || occurs x t) false ts
    then true
    else
      match mot with
      | Some mot ->
        let _, mot = unbind mot in
        let _, mot = unbind_p mot in
        occurs x mot
      | None -> false)
  | Axiom (_, ty) -> occurs x ty


let rec unify t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Var x1, Var x2 -> eq_vars x1 x2
    | Meta x1, Meta x2 -> Meta.equal x1 x2
    | Meta x, _ ->
      if occurs x t2 then false
      else (Meta.set x t2; true)
    | _, Meta x ->
      if occurs x t1 then false
      else (Meta.set x t1; true)
    | Type, Type -> true
    | Linear, Linear -> true
    | TyProd (t1, b1), TyProd (t2, b2) ->
      unify t1 t2 && eq_binder unify b1 b2
    | LnProd (t1, b1), LnProd (t2, b2) ->
      unify t1 t2 && eq_binder unify b1 b2
    | Lambda pb1, Lambda pb2 ->
      eq_binder unify pb1 pb2
    | Fix b1, Fix b2 ->
      eq_binder unify b1 b2
    | App (t11, t12), App (t21, t22) ->
      unify t11 t21 && unify t12 t22
    | LetIn (t1, b1), LetIn (t2, b2) ->
      unify t1 t2 && eq_binder unify b1 b2
    | TCons (id1, ts1), TCons (id2, ts2) ->
      Id.equal id1 id2 && List.equal unify ts1 ts2
    | DCons (id1, ts1), DCons (id2, ts2) ->
      Id.equal id1 id2 && List.equal unify ts1 ts2
    | Match (t1, mot1, ps1), Match (t2, mot2, ps2) ->
      unify t1 t2 &&
      Option.equal (eq_binder (eq_binder_p unify)) mot1 mot2 &&
      List.equal (eq_binder_p unify) ps1 ps2
    | Axiom (id1, ty1), Axiom (id2, ty2) ->
      Id.equal id1 id2 && unify ty1 ty2
    | _ -> false