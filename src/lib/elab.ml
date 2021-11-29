open Bindlib
open Format
open Names
open Terms
open Context
open Equality
open Unify
open Util
open Exceptions

let rec infer_sort v_ctx id_ctx eqns mmap ty =
  let t, eqns, mmap = infer v_ctx id_ctx eqns mmap ty in
  match whnf t with
  | Sort srt -> (srt, eqns, mmap)
  | _ -> raise (UnexpectedTypeExn (ty, t))

and infer v_ctx id_ctx eqns mmap t =
  let h, _ = spine t in
  match h with
  | Meta _ ->
    let xs, _ = Util.unzip (VarMap.bindings v_ctx) in
    let ty = _App' (_Meta (Meta.mk ())) (List.map _Var xs) in
    (unbox ty, eqns, mmap)
  | _ -> (
    match t with
    | Var x -> (
      let ty, srt = find_var x v_ctx in
      match srt with
      | U -> (ty, eqns, mmap)
      | L -> (ty, eqns, mmap))
    | Meta x -> raise (InferMetaExn x)
    | Ann (t, ty) -> (
      let _, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      match t with
      | LetIn (t, b) ->
        let x, ub = unbind b in
        let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
        let eqns, mmap = check v_ctx id_ctx eqns mmap (LetIn (t, b)) ty in
        (ty, eqns, mmap)
      | _ ->
        let eqns, mmap = check v_ctx id_ctx eqns mmap t ty in
        (ty, eqns, mmap))
    | Sort srt -> (
      match srt with
      | U -> (Sort U, eqns, mmap)
      | L -> (Sort U, eqns, mmap))
    | Arrow (ty, b) ->
      let x, ub = unbind b in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let _, eqns, mmap =
        infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub
      in
      (Sort U, eqns, mmap)
    | Lolli (ty, b) ->
      let x, ub = unbind b in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let _, eqns, mmap =
        infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub
      in
      (Sort L, eqns, mmap)
    | Lambda _ -> (Meta (Meta.mk ()), eqns, mmap)
    | Fix _ -> (Meta (Meta.mk ()), eqns, mmap)
    | App (t1, t2) -> (
      let ty1, eqns, mmap = infer v_ctx id_ctx eqns mmap t1 in
      match whnf ty1 with
      | Arrow (ty, b) ->
        let eqns, mmap = check v_ctx id_ctx eqns mmap t2 ty in
        (subst b t2, eqns, mmap)
      | Lolli (ty, b) ->
        let eqns, mmap = check v_ctx id_ctx eqns mmap t2 ty in
        (subst b t2, eqns, mmap)
      | _ -> raise (InferAppExn t))
    | LetIn (t, b) ->
      let ty1, eqns, mmap = infer v_ctx id_ctx eqns mmap t in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty1 in
      let mmap = unify mmap eqns in
      let t = resolve mmap t in
      let ty1 = resolve mmap ty1 in
      let ty2, eqns, mmap =
        if srt = U then
          infer v_ctx id_ctx eqns mmap (subst b t)
        else
          let x, ub = unbind b in
          infer (VarMap.add x (ty1, srt) v_ctx) id_ctx eqns mmap ub
      in
      (ty2, eqns, mmap)
    | Ind (id, ts) ->
      let ind = find_id id (id_ctx : id_ctx) in
      infer_pscope v_ctx id_ctx eqns mmap ts ind.ty
    | Constr (id, ts) ->
      let constr = find_constr id id_ctx in
      infer_pscope v_ctx id_ctx eqns mmap ts constr.ty
    | Match (t, mot, pbs) -> (
      let ty, eqns, mmap = infer v_ctx id_ctx eqns mmap t in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let ty = whnf ty in
      match ty with
      | Ind (id, ts) -> (
        let ind = find_id id id_ctx in
        let cover, eqns, mmap = coverage v_ctx id_ctx eqns mmap pbs ind.cs ts in
        match mot with
        | Mot0 -> (
          let ts, eqns, mmap = infer_cover cover id_ctx eqns mmap in
          match ts with
          | [] -> raise (InferMatchMotiveFailedExn (t, ty))
          | t :: ts ->
            let eqns = List.fold_left (fun acc t' -> (t, t') :: acc) eqns ts in
            (t, eqns, mmap))
        | Mot1 mt ->
          let ty' = subst_p mt ty in
          let eqns, mmap = check_motive cover id_ctx eqns mmap mot srt in
          (ty', eqns, mmap)
        | Mot2 mt ->
          let ty' = subst_p (subst mt t) ty in
          let eqns, mmap = check_motive cover id_ctx eqns mmap mot srt in
          (ty', eqns, mmap))
      | _ -> raise (InferMatchNonInductiveExn t))
    | Axiom (_, ty) ->
      let _, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      (ty, eqns, mmap))

and check v_ctx id_ctx eqns mmap t ty =
  match t with
  | Meta _ -> (eqns, mmap)
  | Lambda b -> (
    let x, ub1 = unbind b in
    match whnf ty with
    | Arrow (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      check v_ctx id_ctx eqns mmap ub1 ub2
    | Lolli (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      check v_ctx id_ctx eqns mmap ub1 ub2
    | _ -> raise (UnexpectedTypeExn (t, ty)))
  | Fix b ->
    let x, ub = unbind b in
    let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
    let v_ctx = VarMap.add x (ty, srt) v_ctx in
    check v_ctx id_ctx eqns mmap ub ty
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
    let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap (LetIn (t, b)) in
    ((ty, ty') :: eqns, mmap)
  | Constr (id, ts) -> (
    match whnf ty with
    | Ind (_, ts') ->
      let constr = find_constr id id_ctx in
      let pscope =
        List.fold_left
          (fun pscope t ->
            match pscope with
            | PBind (ty, pb) -> subst pb (Ann (t, ty))
            | PBase _ -> pscope)
          constr.ty ts'
      in
      let ty', eqns, mmap = infer_pscope v_ctx id_ctx eqns mmap ts pscope in
      ((ty, ty') :: eqns, mmap)
    | _ ->
      let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap t in
      ((ty, ty') :: eqns, mmap))
  | Match (t, mot, pbs) -> (
    match mot with
    | Mot0 -> (
      let ty1, eqns, mmap = infer v_ctx id_ctx eqns mmap t in
      let ty1 = whnf ty1 in
      match ty1 with
      | Ind (id, ts) ->
        let ind = find_id id id_ctx in
        let cover, eqns, mmap = coverage v_ctx id_ctx eqns mmap pbs ind.cs ts in
        check_cover cover id_ctx eqns mmap ty
      | _ -> raise (CheckMatchNonInductiveExn t))
    | _ ->
      let ty', eqns, mmap =
        infer v_ctx id_ctx eqns mmap (Match (t, mot, pbs))
      in
      ((ty, ty') :: eqns, mmap))
  | _ ->
    let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap t in
    ((ty, ty') :: eqns, mmap)

and infer_pscope v_ctx id_ctx eqns mmap ts pscope =
  match (ts, pscope) with
  | t :: ts, PBind (ty, pscope) ->
    let eqns, mmap = check v_ctx id_ctx eqns mmap t ty in
    infer_pscope v_ctx id_ctx eqns mmap ts (subst pscope (Ann (t, ty)))
  | ts, PBase tscope -> infer_tscope v_ctx id_ctx eqns mmap ts tscope
  | _ -> raise (InferPscopeUnevenLength (pscope, List.length ts))

and infer_tscope v_ctx id_ctx eqns mmap ts tscope =
  match (ts, tscope) with
  | t :: ts, TBind (ty, tscope) ->
    let eqns, mmap = check v_ctx id_ctx eqns mmap t ty in
    infer_tscope v_ctx id_ctx eqns mmap ts (subst tscope (Ann (t, ty)))
  | [], TBase ty -> (ty, eqns, mmap)
  | _ -> raise (InferTscopeUnevenLength (tscope, List.length ts))

and coverage v_ctx id_ctx eqns mmap pbs ds ts =
  let rec t_of_p = function
    | PVar x -> Var x
    | PInd (id, ps) -> Ind (id, List.map t_of_p ps)
    | PConstr (id, ps) -> Constr (id, List.map t_of_p ps)
  in
  let rec strip = function
    | PVar x -> x
    | p -> raise (CoverageStripExn p)
  and find id = function
    | constr :: cs ->
      if Id.equal id constr.id then
        (constr, cs)
      else
        let c, cs = find id cs in
        (c, constr :: cs)
    | _ -> raise (UnboundIdExn id)
  and arity_pscope v_ctx eqns mmap pscope ts xs =
    match (pscope, ts) with
    | PBind (ty, pscope), t :: ts ->
      let pscope = subst pscope (Ann (t, ty)) in
      arity_pscope v_ctx eqns mmap pscope ts xs
    | PBase tscope, _ -> arity_tscope v_ctx eqns mmap tscope xs
    | _ -> raise (CoverageArityPscopeExn (pscope, ts))
  and arity_tscope v_ctx eqns mmap tscope xs =
    match (tscope, xs) with
    | TBind (ty, tscope), x :: xs ->
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      let tscope = subst tscope (Var x) in
      let v_ctx, ty, xsrt, eqns, mmap =
        arity_tscope v_ctx eqns mmap tscope xs
      in
      (v_ctx, ty, (x, srt) :: xsrt, eqns, mmap)
    | TBase ty, [] -> (v_ctx, ty, [], eqns, mmap)
    | _ -> raise (CoverageArityTscopeExn (tscope, xs))
  in
  match pbs with
  | pb :: pbs -> (
    let p, ub = unbind_p pb in
    match p with
    | PConstr (id, ps) ->
      let xs = List.map strip ps in
      let t = t_of_p p in
      let constr, ds = find id ds in
      let v_ctx, ty, xsrt, eqns, mmap =
        arity_pscope v_ctx eqns mmap constr.ty ts xs
      in
      let ds, eqns, mmap = coverage v_ctx id_ctx eqns mmap pbs ds ts in
      ((v_ctx, t, ty, ub, xsrt) :: ds, eqns, mmap)
    | _ -> raise (CoverageExn (pb :: pbs)))
  | [] -> (
    match ds with
    | [] -> ([], eqns, mmap)
    | _ -> raise (CoverageExn pbs))

and infer_cover cover id_ctx eqns mmap =
  match cover with
  | (v_ctx, _, _, b, _) :: cover ->
    let ty, eqns, mmap = infer v_ctx id_ctx eqns mmap b in
    let tys, eqns, mmap = infer_cover cover id_ctx eqns mmap in
    (ty :: tys, eqns, mmap)
  | _ -> ([], eqns, mmap)

and check_cover cover id_ctx eqns mmap ty =
  match cover with
  | (v_ctx, _, _, b, _) :: cover ->
    let eqns, mmap = check v_ctx id_ctx eqns mmap b ty in
    check_cover cover id_ctx eqns mmap ty
  | _ -> (eqns, mmap)

and check_motive cover id_ctx eqns mmap mot srt =
  match (mot, srt, cover) with
  | Mot0, _, _ -> raise (CheckMotive mot)
  | Mot1 mt, _, (v_ctx, t, ty, b, _) :: cover ->
    let mt = subst_p mt ty in
    let eqns, mmap = check v_ctx id_ctx eqns mmap b mt in
    check_motive cover id_ctx eqns mmap mot srt
  | Mot2 mt, U, (v_ctx, t, ty, b, _) :: cover ->
    let mt = subst_p (subst mt t) ty in
    let eqns, mmap = check v_ctx id_ctx eqns mmap b mt in
    check_motive cover id_ctx eqns mmap mot srt
  | _ -> (eqns, mmap)

let rec elab_top v_ctx id_ctx eqns mmap top =
  match top with
  | Main t ->
    let ty, eqns, mmap = infer v_ctx id_ctx eqns mmap t in
    let mmap = unify mmap eqns in
    (id_ctx, mmap)
  | Define (t, top) ->
    let ty1, eqns, mmap = infer v_ctx id_ctx eqns mmap t in
    let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty1 in
    let mmap = unify mmap eqns in
    let t = resolve mmap t in
    let ty1 = resolve mmap ty1 in
    let id_ctx, mmap =
      if srt = U then
        elab_top v_ctx id_ctx eqns mmap (subst top t)
      else
        let x, top = unbind top in
        let id_ctx, mmap =
          elab_top (VarMap.add x (ty1, srt) v_ctx) id_ctx eqns mmap top
        in
        (id_ctx, mmap)
    in
    (id_ctx, mmap)
  | Datype (ind, top) ->
    let eqns, mmap = check_pscope v_ctx id_ctx eqns mmap ind.ty U in
    let mmap = unify mmap eqns in
    let ty = unbox (resolve_pscope mmap ind.ty) in
    let id_ctx = IdMap.add ind.id { id = ind.id; ty; cs = [] } id_ctx in
    let eqns, mmap =
      List.fold_left
        (fun (eqns, mmap) constr ->
          let eqns, mmap = check_pscope v_ctx id_ctx eqns mmap constr.ty U in
          param_pscope constr.ty ind.id [];
          (eqns, mmap))
        (eqns, mmap) ind.cs
    in
    let mmap = unify mmap eqns in
    let cs = List.map (fun x -> unbox (resolve_constr mmap x)) ind.cs in
    let id_ctx = IdMap.add ind.id { id = ind.id; ty; cs } id_ctx in
    elab_top v_ctx id_ctx eqns mmap top

and cmp_sort t1 t2 =
  match (t1, t2) with
  | U, L -> false
  | _ -> true

and min_sort t1 t2 =
  match t1 with
  | U -> t2
  | L -> t1

and check_pscope v_ctx id_ctx eqns mmap pscope srt =
  match pscope with
  | PBase tscope -> check_tscope v_ctx id_ctx eqns mmap tscope srt
  | PBind (t, pscope) ->
    let x, pscope = unbind pscope in
    let srt', eqns, mmap = infer_sort v_ctx id_ctx eqns mmap t in
    let v_ctx = VarMap.add x (t, srt) v_ctx in
    check_pscope v_ctx id_ctx eqns mmap pscope (min_sort srt srt')

and check_tscope v_ctx id_ctx eqns mmap tscope srt =
  match tscope with
  | TBase t ->
    let srt', eqns, mmap = infer_sort v_ctx id_ctx eqns mmap t in
    raise_cond (cmp_sort srt' srt) (CheckTscopeExn (t, srt', srt));
    (eqns, mmap)
  | TBind (t, tscope) ->
    let x, tscope = unbind tscope in
    let srt', eqns, mmap = infer_sort v_ctx id_ctx eqns mmap t in
    let v_ctx = VarMap.add x (t, srt') v_ctx in
    check_tscope v_ctx id_ctx eqns mmap tscope (min srt srt')

and param_pscope pscope id xs =
  match pscope with
  | PBase tscope -> param_tscope tscope id (List.rev xs)
  | PBind (_, pscope) ->
    let x, pscope = unbind pscope in
    param_pscope pscope id (x :: xs)

and param_tscope tscope id xs =
  let rec param xs ts =
    match (xs, ts) with
    | [], _ -> ()
    | x :: xs, Var t :: ts ->
      raise_cond (eq_vars x t) (ParamTscopeParamExn (x :: xs, Var t :: ts));
      param xs ts
    | x :: _, t :: _ -> raise (ParamTscopeParamExn (xs, ts))
    | x :: _, [] -> raise (ParamTscopeParamExn (xs, ts))
  in
  match tscope with
  | TBase ty -> (
    match ty with
    | Ind (id', ts) ->
      raise_cond (Id.equal id id') (ParamTscopeExn ty);
      param xs ts
    | _ -> raise (ParamTscopeExn ty))
  | TBind (_, tscope) ->
    let _, tscope = unbind tscope in
    param_tscope tscope id xs

let elab top =
  let _, mmap = elab_top VarMap.empty IdMap.empty [] MetaMap.empty top in
  mmap