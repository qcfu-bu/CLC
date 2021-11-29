open Bindlib
open Names
open Terms
open Context
open Equality
open Basics
open Util
open Exceptions

let rec infer_sort v_ctx id_ctx ty =
  let t, ctx = infer v_ctx id_ctx ty in
  match whnf t with
  | Sort srt ->
    raise_cond (VarMap.is_empty ctx) (NonPureContextExn (ctx, 0));
    srt
  | _ -> raise (UnexpectedTypeExn (ty, t))

and infer v_ctx id_ctx t =
  match t with
  | Meta x -> raise (InferMetaExn x)
  | Ann (t, ty) -> (
    let _ = infer_sort v_ctx id_ctx ty in
    match t with
    | LetIn (t, b) ->
      let x, ub = unbind b in
      let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
      let ctx = check v_ctx id_ctx (LetIn (t, b)) ty in
      (ty, ctx)
    | _ ->
      let ctx = check v_ctx id_ctx t ty in
      (ty, ctx))
  | Var x -> (
    let ty, srt = find_var x v_ctx in
    match srt with
    | U -> (ty, VarMap.empty)
    | L -> (ty, VarMap.singleton x ty))
  | Sort srt -> (Sort U, VarMap.empty)
  | Arrow (ty, b) ->
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let _ = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
    (Sort U, VarMap.empty)
  | Lolli (ty, b) ->
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let _ = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
    (Sort L, VarMap.empty)
  | Lambda b -> raise (InferLambdaExn t)
  | Fix b -> raise (InferFixExn t)
  | App (t1, t2) -> (
    let ty1, ctx1 = infer v_ctx id_ctx t1 in
    match whnf ty1 with
    | Arrow (ty, b) ->
      let srt = infer_sort v_ctx id_ctx ty in
      let ctx2 = check v_ctx id_ctx t2 ty in
      raise_cond
        (match srt with
        | U -> VarMap.is_empty ctx2
        | L -> true)
        (NonPureContextExn (ctx2, 1));
      (subst b t2, merge ctx1 ctx2)
    | Lolli (ty, b) ->
      let srt = infer_sort v_ctx id_ctx ty in
      let ctx2 = check v_ctx id_ctx t2 ty in
      raise_cond
        (match srt with
        | U -> VarMap.is_empty ctx2
        | L -> true)
        (NonPureContextExn (ctx2, 2));
      (subst b t2, merge ctx1 ctx2)
    | _ -> raise (InferAppExn t))
  | LetIn (t, b) ->
    let ty1, ctx1 = infer v_ctx id_ctx t in
    let srt = infer_sort v_ctx id_ctx ty1 in
    let ty2, ctx2 =
      if srt = U then (
        raise_cond (VarMap.is_empty ctx1) (NonPureContextExn (ctx1, 3));
        infer v_ctx id_ctx (subst b t)
      ) else
        let x, ub = unbind b in
        let ty2, ctx2 = infer (VarMap.add x (ty1, srt) v_ctx) id_ctx ub in
        (ty2, remove x ctx2 srt)
    in
    (ty2, merge ctx1 ctx2)
  | Ind (id, ts) ->
    let ind = find_id id (id_ctx : id_ctx) in
    infer_pscope v_ctx id_ctx ts ind.ty
  | Constr (id, ts) ->
    let constr = find_constr id id_ctx in
    infer_pscope v_ctx id_ctx ts constr.ty
  | Match (t, mot, pbs) -> (
    let ty, ctx1 = infer v_ctx id_ctx t in
    let srt = infer_sort v_ctx id_ctx ty in
    let ty = whnf ty in
    match ty with
    | Ind (id, ts) -> (
      let ind = find_id id id_ctx in
      let cover = coverage v_ctx id_ctx pbs ind.cs ts in
      match (srt, mot) with
      | _, Mot0 -> (
        let ctxs = infer_cover cover id_ctx in
        match ctxs with
        | [] -> raise (InferMatchMotiveFailedExn (t, ty))
        | (t, ctx2) :: ctxs ->
          List.iter
            (fun (t', ctx) ->
              raise_cond (equal t t') (UnexpectedTypeExn (t, t'));
              raise_cond (Context.equal ctx2 ctx)
                (UnexpectedContextExn (ctx1, ctx2)))
            ctxs;
          (t, merge ctx1 ctx2))
      | _, Mot1 mt -> (
        let ty' = subst_p mt ty in
        let ctxs = check_motive cover id_ctx mot srt in
        match ctxs with
        | [] -> (ty', ctx1)
        | ctx2 :: ctxs ->
          List.iter
            (fun ctx ->
              raise_cond (Context.equal ctx2 ctx)
                (UnexpectedContextExn (ctx1, ctx2)))
            ctxs;
          (ty', merge ctx1 ctx2))
      | U, Mot2 mt -> (
        let ty' = subst_p (subst mt t) ty in
        let ctxs = check_motive cover id_ctx mot srt in
        match ctxs with
        | [] -> (ty', ctx1)
        | ctx2 :: ctxs ->
          List.iter
            (fun ctx ->
              raise_cond (Context.equal ctx2 ctx)
                (UnexpectedContextExn (ctx1, ctx2)))
            ctxs;
          raise_cond (VarMap.is_empty ctx1) (NonPureContextExn (ctx1, 4));
          (ty', merge ctx1 ctx2))
      | _ -> raise (InferMatchLinearMotiveExn (t, ty)))
    | _ -> raise (InferMatchNonInductiveExn t))
  | Axiom (_, ty) ->
    let _ = infer_sort v_ctx id_ctx ty in
    (ty, VarMap.empty)

and check v_ctx id_ctx t ty =
  match t with
  | Meta x -> raise (CheckMetaExn x)
  | Lambda b -> (
    let x, ub1 = unbind b in
    match whnf ty with
    | Arrow (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt = infer_sort v_ctx id_ctx ty in
      let ctx = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub1 ub2 in
      let ctx = remove x ctx srt in
      raise_cond (VarMap.is_empty ctx) (NonPureContextExn (ctx, 5));
      ctx
    | Lolli (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt = infer_sort v_ctx id_ctx ty in
      let ctx = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub1 ub2 in
      remove x ctx srt
    | _ -> raise (UnexpectedTypeExn (t, ty)))
  | Fix b ->
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let ctx = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub ty in
    raise_cond (VarMap.is_empty ctx) (NonPureContextExn (ctx, 6));
    ctx
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
    let ty', ctx = infer v_ctx id_ctx (LetIn (t, b)) in
    raise_cond (equal ty ty') (UnexpectedTypeExn (ty, ty'));
    ctx
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
      let ty', ctx = infer_pscope v_ctx id_ctx ts pscope in
      raise_cond (equal ty ty') (UnexpectedTypeExn (t, ty));
      ctx
    | _ ->
      let ty', ctx = infer v_ctx id_ctx t in
      raise_cond (equal ty ty') (UnexpectedTypeExn (t, ty));
      ctx)
  | Match (t, mot, pbs) -> (
    match mot with
    | Mot0 -> (
      let ty1, ctx1 = infer v_ctx id_ctx t in
      let ty1 = whnf ty1 in
      match ty1 with
      | Ind (id, ts) -> (
        let ind = find_id id id_ctx in
        let cover = coverage v_ctx id_ctx pbs ind.cs ts in
        let ctxs = check_cover cover id_ctx ty in
        match ctxs with
        | [] -> ctx1
        | ctx2 :: ctxs ->
          List.iter
            (fun ctx ->
              raise_cond (Context.equal ctx2 ctx)
                (UnexpectedContextExn (ctx2, ctx)))
            ctxs;
          merge ctx1 ctx2)
      | _ -> raise (CheckMatchNonInductiveExn t))
    | _ ->
      let ty', ctx = infer v_ctx id_ctx (Match (t, mot, pbs)) in
      raise_cond (equal ty ty') (UnexpectedTypeExn (t, ty));
      ctx)
  | _ ->
    let ty', ctx = infer v_ctx id_ctx t in
    raise_cond (equal ty ty') (UnexpectedTypeExn (t, ty));
    ctx

and infer_pscope v_ctx id_ctx ts pscope =
  match (ts, pscope) with
  | t :: ts, PBind (ty, pscope) ->
    let srt = infer_sort v_ctx id_ctx ty in
    let ctx1 = check v_ctx id_ctx t ty in
    let ty, ctx2 = infer_pscope v_ctx id_ctx ts (subst pscope (Ann (t, ty))) in
    raise_cond
      (match srt with
      | U -> VarMap.is_empty ctx1
      | L -> true)
      (NonPureContextExn (ctx1, 7));
    (ty, merge ctx1 ctx2)
  | ts, PBase tscope -> infer_tscope v_ctx id_ctx ts tscope
  | _ -> raise (InferPscopeUnevenLength (pscope, List.length ts))

and infer_tscope v_ctx id_ctx ts tscope =
  match (ts, tscope) with
  | t :: ts, TBind (ty, tscope) ->
    let srt = infer_sort v_ctx id_ctx ty in
    let ctx1 = check v_ctx id_ctx t ty in
    let ty, ctx2 = infer_tscope v_ctx id_ctx ts (subst tscope (Ann (t, ty))) in
    raise_cond
      (match srt with
      | U -> VarMap.is_empty ctx1
      | L -> true)
      (NonPureContextExn (ctx1, 8));
    (ty, merge ctx1 ctx2)
  | [], TBase ty -> (ty, VarMap.empty)
  | _ -> raise (InferTscopeUnevenLength (tscope, List.length ts))

and coverage v_ctx id_ctx pbs cs ts =
  let rec t_of_p = function
    | PVar x -> Var x
    | PInd (id, ps) -> Ind (id, List.map t_of_p ps)
    | PConstr (id, ps) -> Constr (id, List.map t_of_p ps)
  in
  let strip = function
    | PVar x -> x
    | p -> raise (CoverageStripExn p)
  in
  let rec find id = function
    | constr :: cs ->
      if Id.equal id constr.id then
        (constr, cs)
      else
        let c, cs = find id cs in
        (c, constr :: cs)
    | _ -> raise (UnboundIdExn id)
  in
  let rec arity_pscope v_ctx pscope ts xs =
    match (pscope, ts) with
    | PBind (ty, pscope), t :: ts ->
      let pscope = subst pscope (Ann (t, ty)) in
      let v_ctx, ty, xsrt = arity_pscope v_ctx pscope ts xs in
      (v_ctx, ty, xsrt)
    | PBase tscope, _ -> arity_tscope v_ctx tscope xs
    | _ -> raise (CoverageArityPscopeExn (pscope, ts))
  and arity_tscope v_ctx tscope xs =
    match (tscope, xs) with
    | TBind (ty, tscope), x :: xs ->
      let srt = infer_sort v_ctx id_ctx ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      let tscope = subst tscope (Var x) in
      let v_ctx, ty, xsrt = arity_tscope v_ctx tscope xs in
      (v_ctx, ty, (x, srt) :: xsrt)
    | TBase ty, [] -> (v_ctx, ty, [])
    | _ -> raise (CoverageArityTscopeExn (tscope, xs))
  in
  match pbs with
  | pb :: pbs -> (
    let p, ub = unbind_p pb in
    match p with
    | PConstr (id, ps) ->
      let xs = List.map strip ps in
      let t = t_of_p p in
      let c, cs = find id cs in
      let v_ctx, ty, xsrt = arity_pscope v_ctx c.ty ts xs in
      let cs = coverage v_ctx id_ctx pbs cs ts in
      (v_ctx, t, ty, ub, xsrt) :: cs
    | _ -> raise (CoverageExn (pb :: pbs)))
  | [] -> (
    match cs with
    | [] -> []
    | _ -> raise (CoverageExn pbs))

and infer_cover cover id_ctx =
  match cover with
  | (v_ctx, _, _, b, xsrt) :: cover ->
    let ty, ctx = infer v_ctx id_ctx b in
    let ctx = List.fold_left (fun ctx (x, srt) -> remove x ctx srt) ctx xsrt in
    (ty, ctx) :: infer_cover cover id_ctx
  | _ -> []

and check_cover cover id_ctx ty =
  match cover with
  | (v_ctx, _, _, b, xsrt) :: cover ->
    let ctx = check v_ctx id_ctx b ty in
    let ctx = List.fold_left (fun ctx (x, srt) -> remove x ctx srt) ctx xsrt in
    ctx :: check_cover cover id_ctx ty
  | _ -> []

and check_motive cover id_ctx mot srt =
  match (mot, srt, cover) with
  | Mot0, _, _ -> raise (CheckMotive mot)
  | Mot1 mt, _, (v_ctx, t, ty, b, xsrt) :: cover ->
    let mt = subst_p mt ty in
    let ctx = check v_ctx id_ctx b mt in
    let ctx = List.fold_left (fun ctx (x, srt) -> remove x ctx srt) ctx xsrt in
    ctx :: check_motive cover id_ctx mot srt
  | Mot2 mt, U, (v_ctx, t, ty, b, xsrt) :: cover ->
    let mt = subst_p (subst mt t) ty in
    let ctx = check v_ctx id_ctx b mt in
    let ctx = List.fold_left (fun ctx (x, srt) -> remove x ctx srt) ctx xsrt in
    ctx :: check_motive cover id_ctx mot srt
  | _ -> []

let rec infer_top v_ctx id_ctx top =
  match top with
  | Main t ->
    let ctx = check v_ctx id_ctx t (Ind (_unit, [])) in
    let _ = Format.printf "main(%a)@.@." pp' ctx in
    (ctx, id_ctx)
  | Define (t, top) ->
    let ty1, ctx1 = infer v_ctx id_ctx t in
    let srt = infer_sort v_ctx id_ctx ty1 in
    let ctx2, id_ctx =
      if srt = U then (
        raise_cond (VarMap.is_empty ctx1) (NonPureContextExn (ctx1, 9));
        infer_top v_ctx id_ctx (subst top t)
      ) else
        let x, top = unbind top in
        let ctx, id_ctx =
          infer_top (VarMap.add x (ty1, srt) v_ctx) id_ctx top
        in
        (remove x ctx srt, id_ctx)
    in
    (merge ctx1 ctx2, id_ctx)
  | Datype (ind, top) ->
    check_pscope v_ctx id_ctx ind.ty U;
    let id_ctx = IdMap.add ind.id { ind with cs = [] } id_ctx in
    List.iter
      (fun constr ->
        check_pscope v_ctx id_ctx constr.ty U;
        param_pscope constr.ty ind.id [])
      ind.cs;
    let id_ctx = IdMap.add ind.id ind id_ctx in
    infer_top v_ctx id_ctx top

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
    | x :: xs, Var y :: ts ->
      raise_cond (eq_vars x y) (ParamTscopeParamExn (x :: xs, Var y :: ts));
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

and cmp_sort t1 t2 =
  match (t1, t2) with
  | U, L -> false
  | _ -> true

and min_sort t1 t2 =
  match t1 with
  | U -> t2
  | L -> t1

and check_pscope v_ctx id_ctx pscope srt =
  match pscope with
  | PBase tscope -> check_tscope v_ctx id_ctx tscope srt
  | PBind (ty, pscope) ->
    let x, pscope = unbind pscope in
    let srt' = infer_sort v_ctx id_ctx ty in
    let v_ctx = VarMap.add x (ty, srt) v_ctx in
    check_pscope v_ctx id_ctx pscope (min_sort srt srt')

and check_tscope v_ctx id_ctx tscope srt =
  match tscope with
  | TBase ty ->
    let srt' = infer_sort v_ctx id_ctx ty in
    raise_cond (cmp_sort srt' srt) (CheckTscopeExn (ty, srt', srt))
  | TBind (ty, tscope) ->
    let x, tscope = unbind tscope in
    let srt' = infer_sort v_ctx id_ctx ty in
    let v_ctx = VarMap.add x (ty, srt') v_ctx in
    check_tscope v_ctx id_ctx tscope (min srt srt')

let infer top =
  let ctx, _ = infer_top VarMap.empty IdMap.empty top in
  raise_cond (VarMap.is_empty ctx) (NonPureContextExn (ctx, 10))
