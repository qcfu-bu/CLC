open Bindlib
open Names
open Terms

let rec aeq t1 t2 =
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Meta x1, Meta x2 -> Meta.equal x1 x2
  | Ann (t1, ty1), Ann (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Sort t1, Sort t2 -> t1 = t2
  | Arrow (t1, b1), Arrow (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Lolli (t1, b1), Lolli (t2, b2) ->
    aeq t1 t2 && eq_binder aeq b1 b2
  | Lambda (_, b1), Lambda (_, b2) -> 
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
  | Meta _ -> t
  | Ann (t, _) -> whnf t
  | Sort _ -> t
  | Arrow _ -> t
  | Lolli _ -> t
  | Lambda _ -> t
  | Fix _ -> t
  | App (t1, t2) -> (
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1 with
    | Lambda (_, b) -> whnf (subst b t2)
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
  | Meta _ -> t
  | Ann (t, _) -> nf t
  | Sort _ -> t
  | Arrow (t, b) ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    Arrow (nf t, b)
  | Lolli (t, b) ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    Lolli (nf t, b)
  | Lambda (opt, b) -> (
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    match opt with
    | Some t -> Lambda (Some (nf t), b)
    | None -> Lambda (None, b))
  | Fix b ->
    let x, b = unbind b in
    let b = unbox (bind_var x (lift (nf b))) in
    Fix b
  | App (t1, t2) -> (
    let t1 = nf t1 in
    let t2 = nf t2 in
    match t1 with
    | Lambda (_, b) -> nf (subst b t2)
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

let rec equal t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Var x1, Var x2 -> eq_vars x1 x2
    | Ann (t1, ty1), Ann (t2, ty2) ->
      equal t1 t2 && equal ty1 ty2
    | Sort srt1, Sort srt2 -> srt1 = srt2
    | Arrow (t1, b1), Arrow (t2, b2) ->
      equal t1 t2 && eq_binder equal b1 b2
    | Lolli (t1, b1), Lolli (t2, b2) ->
      equal t1 t2 && eq_binder equal b1 b2
    | Lambda (_, pb1), Lambda (_, pb2) ->
      eq_binder equal pb1 pb2
    | Fix b1, Fix b2 ->
      eq_binder equal b1 b2
    | App (t11, t12), App (t21, t22) ->
      equal t11 t21 && equal t12 t22
    | LetIn (t1, pb1), LetIn (t2, pb2) ->
      equal t1 t2 && eq_binder equal pb1 pb2
    | TCons (id1, ts1), TCons (id2, ts2) ->
      Id.equal id1 id2 && List.equal equal ts1 ts2
    | DCons (id1, ts1), DCons (id2, ts2) ->
      Id.equal id1 id2 && List.equal equal ts1 ts2
    | Match (t1, opt1, ps1), Match (t2, opt2, ps2) ->
      equal t1 t2 && 
      Option.equal (eq_binder (eq_binder_p equal)) opt1 opt2 &&
      List.equal (eq_binder_p equal) ps1 ps2
    | Axiom (id1, ty1), Axiom (id2, ty2) ->
      Id.equal id1 id2 && equal ty1 ty2
    | _ -> false