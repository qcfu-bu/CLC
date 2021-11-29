open Bindlib
open Format
open Util
open Names
open Terms
open Equality
open Exceptions

module VarSet = Set.Make (struct
  type t = Terms.t var

  let compare = compare_vars
end)

module MetaMap = Map.Make (Meta)

let union m1 m2 =
  MetaMap.union
    (fun _ (x, ord1) (y, ord2) ->
      if ord1 < ord2 then
        Some (y, ord2)
      else
        Some (x, ord1))
    m1 m2

let pp_set fmt s = VarSet.iter (fun x -> fprintf fmt "%a " pp_v x) s

let pp_mmap fmt m =
  MetaMap.iter (fun x (t, _) -> fprintf fmt "%a := %a@." Meta.pp x Terms.pp t) m

let pp_eqn n fmt eqns =
  List.iter
    (fun (t1, t2) ->
      fprintf fmt "eqn%d := %a ?= %a@." n Terms.pp (whnf t1) Terms.pp (whnf t2);
      fprintf fmt "-------------------------------------------------------@.")
    eqns

let rec fv ctx t =
  match t with
  | Var x -> (
    match VarSet.find_opt x ctx with
    | Some _ -> VarSet.empty
    | None -> VarSet.singleton x)
  | Meta _ -> VarSet.empty
  | Ann (t, ty) -> VarSet.union (fv ctx t) (fv ctx ty)
  | Sort _ -> VarSet.empty
  | Arrow (ty, b) ->
    let x, ub = unbind b in
    let fv1 = fv ctx ty in
    let fv2 = fv (VarSet.add x ctx) ub in
    VarSet.union fv1 fv2
  | Lolli (ty, b) ->
    let x, ub = unbind b in
    let fv1 = fv ctx ty in
    let fv2 = fv (VarSet.add x ctx) ub in
    VarSet.union fv1 fv2
  | Lambda b ->
    let x, ub = unbind b in
    fv (VarSet.add x ctx) ub
  | Fix b ->
    let x, ub = unbind b in
    fv (VarSet.add x ctx) ub
  | App (t1, t2) -> VarSet.union (fv ctx t1) (fv ctx t2)
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let fv1 = fv ctx t in
    let fv2 = fv (VarSet.add x ctx) ub in
    VarSet.union fv1 fv2
  | Ind (_, ts) ->
    let ctxs = List.map (fv ctx) ts in
    List.fold_left VarSet.union VarSet.empty ctxs
  | Constr (_, ts) ->
    let ctxs = List.map (fv ctx) ts in
    List.fold_left VarSet.union VarSet.empty ctxs
  | Match (t, mot, pbs) -> (
    let fv1 = fv ctx t in
    let fv2 =
      List.fold_left
        (fun acc pb ->
          let p, ub = unbind_p pb in
          let xs = list_of_p p in
          let ctx = VarSet.union ctx (VarSet.of_list xs) in
          VarSet.union acc (fv ctx ub))
        VarSet.empty pbs
    in
    let res = VarSet.union fv1 fv2 in
    match mot with
    | Mot0 -> res
    | Mot1 mt ->
      let p, ub = unbind_p mt in
      let xs = list_of_p p in
      let ctx = VarSet.union ctx (VarSet.of_list xs) in
      let fv3 = fv ctx ub in
      VarSet.union res fv3
    | Mot2 mt ->
      let x, pb = unbind mt in
      let p, ub = unbind_p pb in
      let xs = list_of_p p in
      let ctx = VarSet.add x ctx in
      let ctx = VarSet.union ctx (VarSet.of_list xs) in
      let fv3 = fv ctx ub in
      VarSet.union res fv3)
  | Axiom (_, ty) -> fv ctx ty

let rec occurs x t =
  match t with
  | Var _ -> false
  | Meta y -> Meta.equal x y
  | Ann (t, ty) -> occurs x t || occurs x ty
  | Sort _ -> false
  | Arrow (t, b) ->
    let _, ub = unbind b in
    occurs x t || occurs x ub
  | Lolli (t, b) ->
    let _, ub = unbind b in
    occurs x t || occurs x ub
  | Lambda b ->
    let _, ub = unbind b in
    occurs x ub
  | Fix b ->
    let _, ub = unbind b in
    occurs x ub
  | App (t1, t2) -> occurs x t1 || occurs x t2
  | LetIn (t, b) ->
    let _, ub = unbind b in
    occurs x t || occurs x ub
  | Ind (_, ts) -> List.fold_left (fun acc t -> acc || occurs x t) false ts
  | Constr (_, ts) -> List.fold_left (fun acc t -> acc || occurs x t) false ts
  | Match (t, mot, pbs) -> (
    let ts = List.map (fun pb -> snd (unbind_p pb)) pbs in
    if occurs x t || List.fold_left (fun acc t -> acc || occurs x t) false ts
    then
      true
    else
      match mot with
      | Mot0 -> false
      | Mot1 mt ->
        let _, mt = unbind_p mt in
        occurs x mt
      | Mot2 mt ->
        let _, mt = unbind mt in
        let _, mt = unbind_p mt in
        occurs x mt)
  | Axiom (_, ty) -> occurs x ty

let rec simpl eqn =
  let t1, t2 = eqn in
  if equal t1 t2 then
    []
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    let h1, sp1 = spine t1 in
    let h2, sp2 = spine t2 in
    match (h1, h2) with
    | Var x1, Var x2 ->
      if eq_vars x1 x2 then
        List.fold_left
          (fun acc (t1, t2) -> acc @ simpl (t1, t2))
          [] (Util.zip sp1 sp2)
      else
        failwith (asprintf "%a != %a" pp_v x1 pp_v x2)
    | Meta _, _ -> [ eqn ]
    | _, Meta _ -> [ (t2, t1) ]
    | Sort t1, Sort t2 ->
      if t1 = t2 then
        []
      else
        raise (UnificationFailure (Sort t1, Sort t2))
    | Arrow (ty1, b1), Arrow (ty2, b2) ->
      let _, ub1, ub2 = unbind2 b1 b2 in
      let eqn1 = simpl (ty1, ty2) in
      let eqn2 = simpl (ub1, ub2) in
      eqn1 @ eqn2
    | Lolli (ty1, b1), Lolli (ty2, b2) ->
      let _, ub1, ub2 = unbind2 b1 b2 in
      let eqn1 = simpl (ty1, ty2) in
      let eqn2 = simpl (ub1, ub2) in
      eqn1 @ eqn2
    | Lambda b1, Lambda b2 ->
      let _, ub1, ub2 = unbind2 b1 b2 in
      simpl (ub1, ub2)
    | Fix b1, Fix b2 ->
      let _, ub1, ub2 = unbind2 b1 b2 in
      simpl (ub1, ub2)
    | LetIn (t1, b1), LetIn (t2, b2) ->
      let _, ub1, ub2 = unbind2 b1 b2 in
      let eqn1 = simpl (t1, t2) in
      let eqn2 = simpl (ub1, ub2) in
      eqn1 @ eqn2
    | Ind (id1, ts1), Ind (id2, ts2) ->
      if Id.equal id1 id2 then
        List.fold_left
          (fun acc (t1, t2) -> acc @ simpl (t1, t2))
          [] (Util.zip ts1 ts2)
      else
        raise (UnificationFailure (t1, t2))
    | Constr (id1, ts1), Constr (id2, ts2) ->
      if Id.equal id1 id2 then
        List.fold_left
          (fun acc (t1, t2) -> acc @ simpl (t1, t2))
          [] (Util.zip ts1 ts2)
      else
        raise (UnificationFailure (t1, t2))
    | Match (t1, mot1, ps1), Match (t2, mot2, ps2) ->
      let eqn1 = simpl (t1, t2) in
      let eqn2 =
        match (mot1, mot2) with
        | Mot0, Mot0 -> []
        | Mot1 mt1, Mot1 mt2 ->
          let _, ub1, ub2 = unbind_p2 mt1 mt2 in
          simpl (ub1, ub2)
        | Mot2 mt1, Mot2 mt2 ->
          let _, pb1, pb2 = unbind2 mt1 mt2 in
          let _, ub1, ub2 = unbind_p2 pb1 pb2 in
          simpl (ub1, ub2)
        | _ -> raise (UnificationFailure (t1, t2))
      in
      let eqn3 =
        List.fold_left
          (fun acc (pb1, pb2) ->
            let _, ub1, ub2 = unbind_p2 pb1 pb2 in
            acc @ simpl (ub1, ub2))
          [] (Util.zip ps1 ps2)
      in
      eqn1 @ eqn2 @ eqn3
    | Axiom (id1, ty1), Axiom (id2, ty2) ->
      if Id.equal id1 id2 then
        let eqn1 = simpl (ty1, ty2) in
        let eqn2 =
          List.fold_left
            (fun acc (t1, t2) -> acc @ simpl (t1, t2))
            [] (Util.zip sp1 sp2)
        in
        eqn1 @ eqn2
      else
        failwith (asprintf "%a != %a" Terms.pp t1 Terms.pp t2)
    | _ -> raise (UnificationFailure (t1, t2))

let solve eqn =
  let strip sp =
    List.map
      (fun t ->
        match t with
        | Var x -> x
        | _ -> mk "")
      sp
  in
  let t1, t2 = eqn in
  let t1 = whnf t1 in
  let t2 = whnf t2 in
  let h1, sp1 = spine t1 in
  let h2, sp2 = spine t2 in
  match (h1, h2) with
  | Meta x1, Meta x2 ->
    let xs = strip sp1 in
    let ys = strip sp2 in
    let ctx = VarSet.inter (VarSet.of_list xs) (VarSet.of_list ys) in
    let zs = List.map _Var (VarSet.elements ctx) in
    let xs =
      List.map
        (fun x ->
          match VarSet.find_opt x ctx with
          | Some _ -> x
          | None -> mk "")
        xs
    in
    let ys =
      List.map
        (fun x ->
          match VarSet.find_opt x ctx with
          | Some _ -> x
          | None -> mk "")
        ys
    in
    let t = _Meta (Meta.mk ()) in
    let t = _App' t zs in
    let t1 = unbox (_Lambda' xs t) in
    let t2 = unbox (_Lambda' ys t) in
    let res = MetaMap.empty in
    let res = MetaMap.add x1 (t1, 0) res in
    let res = MetaMap.add x2 (t2, 0) res in
    res
  | Meta x, _ ->
    raise_cond (not (occurs x t2)) (OccursCheckFailure (x, t2));
    let xs = strip sp1 in
    let ctx' = fv VarSet.empty t2 in
    if VarSet.subset ctx' (VarSet.of_list xs) then
      let t = unbox (_Lambda' xs (lift t2)) in
      MetaMap.singleton x (t, 1)
    else
      failwith (asprintf "cannot unify %a = %a" Meta.pp x Terms.pp t2)
  | _ ->
    failwith (asprintf "non-simpl equation(%a == %a)" Terms.pp t1 Terms.pp t2)

let rec resolve mmap t =
  let h, sp = spine t in
  match h with
  | Meta x -> (
    try
      let h = fst (MetaMap.find x mmap) in
      let sp = List.map lift sp in
      let t = unbox (_App' (lift h) sp) in
      resolve mmap (whnf t)
    with
    | _ -> t)
  | _ -> (
    match t with
    | Var _ -> t
    | Ann (t, ty) -> Ann (resolve mmap t, resolve mmap ty)
    | Sort _ -> t
    | Arrow (ty, b) ->
      let x, ub = unbind b in
      let ty = resolve mmap ty in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      Arrow (ty, b)
    | Lolli (ty, b) ->
      let x, ub = unbind b in
      let ty = resolve mmap ty in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      Lolli (ty, b)
    | Lambda b ->
      let x, ub = unbind b in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      Lambda b
    | Fix b ->
      let x, ub = unbind b in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      Fix b
    | App (t1, t2) ->
      let t1 = resolve mmap t1 in
      let t2 = resolve mmap t2 in
      App (t1, t2)
    | LetIn (t, b) ->
      let t = resolve mmap t in
      let x, ub = unbind b in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      LetIn (t, b)
    | Ind (id, ts) ->
      let ts = List.map (resolve mmap) ts in
      Ind (id, ts)
    | Constr (id, ts) ->
      let ts = List.map (resolve mmap) ts in
      Constr (id, ts)
    | Match (t, mot, pbs) ->
      let t = resolve mmap t in
      let mot =
        match mot with
        | Mot0 -> Mot0
        | Mot1 mt ->
          let p, ub = unbind_p mt in
          let ub = resolve mmap ub in
          let mt = bind_p p (lift ub) in
          Mot1 (unbox mt)
        | Mot2 mt ->
          let x, pb = unbind mt in
          let p, ub = unbind_p pb in
          let ub = resolve mmap ub in
          let mt = bind_var x (bind_p p (lift ub)) in
          Mot2 (unbox mt)
      in
      let pbs =
        List.map
          (fun pb ->
            let p, ub = unbind_p pb in
            let ub = resolve mmap ub in
            unbox (bind_p p (lift ub)))
          pbs
      in
      Match (t, mot, pbs)
    | Axiom (id, ty) -> Axiom (id, resolve mmap ty)
    | _ -> failwith "meta-head")

let rec resolve_top mmap top =
  match top with
  | Main t ->
    let t = resolve mmap t in
    _Main (lift t)
  | Define (t, b) ->
    let x, ub = unbind b in
    let t = resolve mmap t in
    let ub = resolve_top mmap ub in
    let b = bind_var x ub in
    _Define (lift t) b
  | Datype (ind, tp) ->
    let ind = resolve_ind mmap ind in
    let tp = resolve_top mmap tp in
    _Datype ind tp

and resolve_ind mmap ind =
  let ty = resolve_pscope mmap ind.ty in
  let cs = List.map (resolve_constr mmap) ind.cs in
  let cs = box_list cs in
  _ind ind.id ty cs

and resolve_constr mmap constr =
  let ty = resolve_pscope mmap constr.ty in
  _constr constr.id ty

and resolve_pscope mmap pscope =
  match pscope with
  | PBase tscope -> _PBase (resolve_tscope mmap tscope)
  | PBind (t, b) ->
    let x, ub = unbind b in
    let t = resolve mmap t in
    let ub = resolve_pscope mmap ub in
    let b = bind_var x ub in
    _PBind (lift t) b

and resolve_tscope mmap tscope =
  match tscope with
  | TBase t ->
    let t = resolve mmap t in
    _TBase (lift t)
  | TBind (t, b) ->
    let x, ub = unbind b in
    let t = resolve mmap t in
    let ub = resolve_tscope mmap ub in
    let b = bind_var x ub in
    _TBind (lift t) b

let rec unify mmap eqns =
  match List.concat_map simpl eqns with
  | [] -> mmap
  | eqns ->
    let mmaps = List.map solve eqns in
    let mmap = List.fold_left (fun acc mmap -> union acc mmap) mmap mmaps in
    let eqns =
      List.map (fun (t1, t2) -> (resolve mmap t1, resolve mmap t2)) eqns
    in
    unify mmap eqns