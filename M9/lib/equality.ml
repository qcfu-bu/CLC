open Bindlib
open Format
open Names
open Terms
open Context

module VarSet = Set.Make(
  struct
    type t = Terms.t var
    let compare = compare_vars
  end)

let of_map mp =
  let xs = List.map fst (VarMap.bindings mp) in
  VarSet.of_list xs

module MetaMap = Map.Make(Meta)

let union m1 m2 = 
  MetaMap.union 
    (fun _ (x, ord1) (y, ord2) -> 
      if ord1 < ord2 
      then Some (y, ord2) 
      else Some (x, ord1)) 
    m1 m2

type eqn = VarSet.t * t * t
let eqns : eqn list ref = ref []

let pp_set fmt s =
  VarSet.iter (fun x ->
    fprintf fmt "%a " pp_v x) s

let pp_mmap fmt m =
  MetaMap.iter 
    (fun x (t, _) ->
      fprintf fmt "%a := %a@." Meta.pp x Terms.pp t) 
    m

let pp_eqn fmt eqns =
  List.iter (fun (ctx, t1, t2) ->
    fprintf fmt "(%a)@." pp_set ctx;
    fprintf fmt "%a ?= %a@.-------------@." Terms.pp t1 Terms.pp t2) eqns


let rec fv ctx t =
  match t with
  | Var x -> (
    match VarSet.find_opt x ctx with
    | Some _ -> VarSet.empty
    | None -> VarSet.singleton x)
  | Meta _ -> VarSet.empty
  | Ann (t, ty) ->
    VarSet.union (fv ctx t) (fv ctx ty)
  | Sort _ -> VarSet.empty
  | TyProd (ty, b) ->
    let x, ub = unbind b in
    let fv1 = fv ctx ty in
    let fv2 = fv (VarSet.add x ctx) ub in
    VarSet.union fv1 fv2
  | LnProd (ty, b) ->
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
  | App (t1, t2) ->
    VarSet.union (fv ctx t1) (fv ctx t2)
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let fv1 = fv ctx t in
    let fv2 = fv (VarSet.add x ctx) ub in
    VarSet.union fv1 fv2
  | TCons (_, ts) ->
    let ctxs = List.map (fv ctx) ts in
    List.fold_left VarSet.union VarSet.empty ctxs
  | DCons (_, ts) ->
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
    | Some mot ->
      let x, pb = unbind mot in
      let p, ub = unbind_p pb in
      let xs = list_of_p p  in
      let ctx = VarSet.add x ctx in
      let ctx = VarSet.union ctx (VarSet.of_list xs) in
      let fv3 = fv ctx ub in
      VarSet.union res fv3
    | None -> res)
  | Axiom (_, ty) -> fv ctx ty

let rec aeq t1 t2 =
  match t1, t2 with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Meta x1, Meta x2 -> Meta.equal x1 x2
  | Ann (t1, ty1), Ann (t2, ty2) ->
    aeq t1 t2 && aeq ty1 ty2
  | Sort t1, Sort t2 -> t1 = t2
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
  | Meta _ -> t
  | Ann (t, _) -> whnf t
  | Sort _ -> t
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
  | Meta _ -> t
  | Ann (t, _) -> nf t
  | Sort _ -> t
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
  | Meta y -> Meta.equal x y
  | Ann (t, ty) ->
    occurs x t || occurs x ty
  | Sort _ -> false
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

let spine t =
  let rec spine_aux t sp =
    match t with
    | App (t1, t2) -> spine_aux t1 (t2 :: sp)
    | _ -> (t, sp)
  in
  spine_aux t []

let equal ctx t1 t2 =
  if aeq t1 t2
  then ()
  else eqns := (ctx, t1, t2) :: !eqns;
  true

let rec simpl eqn =
  let ctx, t1, t2 = eqn in
  if aeq t1 t2 then []
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    let h1, sp1 = spine t1 in
    let h2, sp2 = spine t2 in
    match h1, h2 with
    | Var x1, Var x2 ->
      if eq_vars x1 x2 
      then 
        List.fold_left (fun acc (t1, t2) ->
          acc @ simpl (ctx, t1, t2))
        [] (Util.zip sp1 sp2)
      else failwith (asprintf "%a != %a" pp_v x1 pp_v x2)
    | Meta _, Meta _ ->
      if List.equal aeq sp1 sp2 then []
      else [ eqn ]
    | Meta _, _ -> [ eqn ]
    | _, Meta _ -> [ (ctx, t2, t1) ]
    | Sort t1, Sort t2 ->
      if t1 = t2 
      then []
      else failwith (asprintf "%a != %a" pp_s t1 pp_s t2)
    | TyProd (ty1, b1), TyProd (ty2, b2) ->
      let x, ub1, ub2 = unbind2 b1 b2 in
      let eqn1 = simpl (ctx, ty1, ty2) in
      let eqn2 = simpl (VarSet.add x ctx, ub1, ub2) in
      eqn1 @ eqn2
    | LnProd (ty1, b1), LnProd (ty2, b2) ->
      let x, ub1, ub2 = unbind2 b1 b2 in
      let eqn1 = simpl (ctx, ty1, ty2) in
      let eqn2 = simpl (VarSet.add x ctx, ub1, ub2) in
      eqn1 @ eqn2
    | Lambda b1, Lambda b2 ->
      let x, ub1, ub2 = unbind2 b1 b2 in
      simpl (VarSet.add x ctx, ub1, ub2)
    | Fix b1, Fix b2 ->
      let x, ub1, ub2 = unbind2 b1 b2 in
      simpl (VarSet.add x ctx, ub1, ub2)
    | LetIn (t1, b1), LetIn (t2, b2) ->
      let x, ub1, ub2 = unbind2 b1 b2 in
      let eqn1 = simpl (ctx, t1, t2) in
      let eqn2 = simpl (VarSet.add x ctx, ub1, ub2) in
      eqn1 @ eqn2
    | TCons (id1, ts1), TCons (id2, ts2) ->
      if Id.equal id1 id2
      then
        List.fold_left
          (fun acc (t1, t2) ->
            acc @ simpl (ctx, t1, t2))
        [] (Util.zip ts1 ts2)
      else 
        failwith (asprintf "%a != %a" Terms.pp t1 Terms.pp t2)
    | DCons (id1, ts1), DCons (id2, ts2) ->
      if Id.equal id1 id2
      then
        List.fold_left
          (fun acc (t1, t2) ->
            acc @ simpl (ctx, t1, t2))
        [] (Util.zip ts1 ts2)
      else 
        failwith (asprintf "%a != %a" Terms.pp t1 Terms.pp t2)
    | Match (t1, mot1, ps1), Match (t2, mot2, ps2) ->
      let eqn1 = simpl (ctx, t1, t2) in
      let eqn2 = 
        match mot1, mot2 with
        | Some mot1, Some mot2 ->
          let x, pb1, pb2 = unbind2 mot1 mot2 in
          let p, ub1, ub2 = unbind_p2 pb1 pb2 in
          let xs = list_of_p p in
          let ctx = VarSet.add x ctx in
          let ctx = VarSet.union ctx (VarSet.of_list xs) in
          simpl (ctx, ub1, ub2)
        | None, None -> []
        | _ -> failwith (asprintf "%a != %a" Terms.pp t1 Terms.pp t2)
      in
      let eqn3 =
        List.fold_left 
          (fun acc (pb1, pb2) ->
            let p, ub1, ub2 = unbind_p2 pb1 pb2 in 
            let xs = list_of_p p in
            let ctx = VarSet.union ctx (VarSet.of_list xs) in
            acc @ simpl (ctx, ub1, ub2))
          [] (Util.zip ps1 ps2)
      in
      eqn1 @ eqn2 @ eqn3
    | Axiom (id1, ty1), Axiom (id2, ty2) ->
      if Id.equal id1 id2
      then 
        let eqn1 = simpl (ctx, ty1, ty2) in
        let eqn2 =
          List.fold_left (fun acc (t1, t2) ->
            acc @ simpl (ctx, t1, t2))
          [] (Util.zip sp1 sp2)
        in
        eqn1 @ eqn2
      else failwith (asprintf "%a != %a" Terms.pp t1 Terms.pp t2)
    | _ -> 
      printf "%a != %a@." Terms.pp t1 Terms.pp t2;
      printf "ctx := %a@." pp_set ctx;
      failwith "unfication failure"

let solve eqn =
  let strip sp = 
    List.map (
      fun t ->
        match t with
        | Var x -> x
        | _ -> mk "") sp
  in
  let _, t1, t2 = eqn in
  let t1 = whnf t1 in
  let t2 = whnf t2 in
  let h1, sp1 = spine t1 in
  let h2, sp2 = spine t2 in
  match h1, h2 with
  | Meta x1, Meta x2 ->
    let xs = strip sp1 in
    let ys = strip sp2 in
    let ctx = VarSet.inter (VarSet.of_list xs) (VarSet.of_list xs) in
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
    if occurs x t2
    then failwith (asprintf "%a occurs in %a" Meta.pp x Terms.pp t2)
    else 
      let xs = strip sp1 in
      let ctx' = fv VarSet.empty t2 in
      if VarSet.subset ctx' (VarSet.of_list xs)
      then 
        let t = unbox (_Lambda' xs (lift t2)) in
        MetaMap.singleton x (t, 1)
      else 
        failwith 
          (asprintf "cannot unify %a = %a" Meta.pp x Terms.pp t2)
  | _ -> 
    failwith (asprintf "non-simpl equation(%a == %a)" 
      Terms.pp t1 Terms.pp t2)

let rec resolve mmap t =
  let h, sp = spine t in
  match h with
  | Meta x -> (
    try
      let h = fst (MetaMap.find x mmap) in
      let sp = List.map lift sp in
      let t = unbox (_App' (lift h) sp) in
      resolve mmap (whnf t)
    with _ ->  t)
  | _ -> (
    match t with
    | Var _ -> t
    | Ann (t, ty) ->
      Ann (resolve mmap t, resolve mmap ty)
    | Sort _ -> t
    | TyProd (ty, b) ->
      let x, ub = unbind b in
      let ty = resolve mmap ty in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      TyProd (ty, b)
    | LnProd (ty, b) ->
      let x, ub = unbind b in
      let ty = resolve mmap ty in
      let ub = resolve mmap ub in
      let b = unbox (bind_var x (lift ub)) in
      LnProd (ty, b)
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
    | TCons (id, ts) ->
      let ts = List.map (resolve mmap) ts in
      TCons (id, ts)
    | DCons (id, ts) ->
      let ts = List.map (resolve mmap) ts in
      DCons (id, ts)
    | Match (t, mot, pbs) ->
      let t = resolve mmap t in
      let mot = 
        match mot with
        | Some mot -> 
          let x, pb = unbind mot in
          let p, ub = unbind_p pb in
          let ub = resolve mmap ub in
          let mot = bind_var x (bind_p p (lift ub)) in
          Some (unbox mot)
        | None -> None
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
    | Axiom (id, ty) ->
      Axiom (id, resolve mmap ty)
    | _ -> failwith "meta-head")

let rec resolve_top mmap top =
  match top with
  | Empty -> _Empty
  | Define (t, b) ->
    let x, ub = unbind b in
    let t = resolve mmap t in
    let ub = resolve_top mmap ub in
    let b = bind_var x ub in
    _Define (lift t) b
  | Datype (tcons, tp) ->
    let tcons = resolve_tcons mmap tcons in
    let tp = resolve_top mmap tp in
    _Datype tcons tp

and resolve_tcons mmap tcons =
  let TConstr (id, pscope, dcons) = tcons in
  let pscope = resolve_pscope mmap pscope in
  let dcons = List.map (resolve_dcons mmap) dcons in
  let dcons = box_list dcons in
  _TConstr id pscope dcons

and resolve_dcons mmap dcons = 
  let DConstr (id, pscope) = dcons in
  let pscope = resolve_pscope mmap pscope in
  _DConstr id pscope

and resolve_pscope mmap pscope =
  match pscope with
  | PBase tscope -> 
    _PBase (resolve_tscope mmap tscope)
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

let unify mmap =
  let rec unify_aux mmap eqns =
    match List.concat_map simpl eqns with
    | [] -> mmap
    | eqns ->
      let mmaps = List.map solve eqns in
      let mmap = 
        List.fold_left 
          (fun acc mmap -> union acc mmap) 
          mmap mmaps
      in
      let eqns =
        List.map (fun (ctx, t1, t2) -> 
          (ctx, resolve mmap t1, resolve mmap t2))
        eqns
      in
      unify_aux mmap eqns
  in
  let mmap = unify_aux mmap !eqns in
  eqns := []; mmap