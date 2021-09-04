open Bindlib
open Format
open Names
open Terms
open Context
open Equality
open Unify

let assert_msg cond msg = 
  if cond then ()
  else (prerr_endline msg; assert false)

let cmp_sort t1 t2 =
  match t1, t2 with
  | Type, Linear -> false
  | _ -> true

let min_sort t1 t2 = 
  match t1 with
  | Type -> t2
  | Linear -> t1

let rec infer_sort v_ctx id_ctx ty =
  let srt, ctx, eqns = infer v_ctx id_ctx ty in
  match whnf srt with
  | Sort srt ->
    assert_msg (VarMap.is_empty ctx) "non-clean context for sort";
    (srt, eqns)
  | _ ->
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp srt)

and infer v_ctx id_ctx t =
  let h, _ = spine t in
  match h with
  | Meta _ ->
    let xs, _ = Util.unzip (VarMap.bindings v_ctx) in
    let ty = _App' (_Meta (Meta.mk ())) (List.map _Var xs) in
    (unbox ty, VarMap.empty, [])
  | _ -> (
    match t with
    | Var x -> (
      let ty, srt = find x v_ctx in
      match srt with
      | Type -> (ty, VarMap.empty, [])
      | Linear -> (ty, VarMap.singleton x ty, []))
    | Meta _ -> failwith "infer Meta"
    | Ann (t, ty) -> (
      let _, eqns1 = infer_sort v_ctx id_ctx ty in
      match t with
      | LetIn (t, b) ->
        let x, ub = unbind b in
        let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
        let ctx, eqns2 = check v_ctx id_ctx (LetIn (t, b)) ty in
        (ty, ctx, eqns1 @ eqns2)
      | _ -> 
        let ctx, eqns2 = check v_ctx id_ctx t ty in
        (ty, ctx, eqns1 @ eqns2))
    | Sort srt -> (
      match srt with
      | Type -> (Sort Type, VarMap.empty, [])
      | Linear -> (Sort Type, VarMap.empty, []))
    | TyProd (ty, b) ->
      let x, ub = unbind b in
      let srt, eqns1 = infer_sort v_ctx id_ctx ty in
      let _, eqns2 = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
      (Sort Type, VarMap.empty, eqns1 @ eqns2)
    | LnProd (ty, b) ->
      let x, ub = unbind b in
      let srt, eqns1 = infer_sort v_ctx id_ctx ty in
      let _, eqns2 = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
      (Sort Linear, VarMap.empty, eqns1 @ eqns2)
    | Lambda _ -> failwith (asprintf "infer Lambda(%a)" Terms.pp t)
    | Fix _ -> failwith (asprintf "infer Fix(%a)" Terms.pp t)
    | App (t1, t2) -> (
      let ty1, ctx1, eqns1 = infer v_ctx id_ctx t1 in
      match whnf ty1 with
      | TyProd (ty, b) ->
        let ctx2, eqns2 = check v_ctx id_ctx t2 ty in
        (subst b t2, merge ctx1 ctx2, eqns1 @ eqns2)
      | LnProd (ty, b) ->
        let ctx2, eqns2 = check v_ctx id_ctx t2 ty in
        (subst b t2, merge ctx1 ctx2, eqns1 @ eqns2)
      | _ -> failwith (asprintf "@[infer App(t :=@;<1 2>%a)@]" Terms.pp t))
    | LetIn (t, b) -> (
      let ty1, ctx1, eqns1 = infer v_ctx id_ctx t in
      let srt, eqns = infer_sort v_ctx id_ctx ty1 in
      let ty2, ctx2, eqns2 = 
        if srt = Type && VarMap.is_empty ctx1  then
          infer v_ctx id_ctx (subst b t)
        else
          let x, ub = unbind b in
          let ty2, ctx2, eqns2 =
            infer (VarMap.add x (ty1, srt) v_ctx) id_ctx ub 
          in
          (ty2, remove x ctx2 srt, eqns2)
      in
      (ty2, merge ctx1 ctx2, eqns1 @ eqns2 @ eqns))
    | TCons (id, ts) -> (
      let TConstr (_, pscope, _) = IdMap.find id id_ctx in
      infer_pscope v_ctx id_ctx ts pscope)
    | DCons (id, ts) -> (
      match find_dcons id id_ctx with
      | DConstr (_, PBase tscope) ->
        infer_tscope v_ctx id_ctx ts tscope
      | _ -> failwith (asprintf "infer DCons(%a)" Terms.pp t))
    | Match (t, mot, pbs) -> (
      let ty, ctx1, eqns1 = infer v_ctx id_ctx t in
      let srt, eqns = infer_sort v_ctx id_ctx ty in
      let ty = whnf ty in
      match ty with
      | TCons (id, ts) -> (
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover = coverage v_ctx id_ctx pbs ds ts in
        match mot with
        | Some mot -> (
          let ty' = subst_p (subst mot t) ty in
          let res = check_motive cover id_ctx mot srt in
          match res with
          | [] -> (ty', ctx1, eqns1 @ eqns)
          | (ctx2, eqns2) :: res ->
            let eqns2 =
              List.fold_left
                (fun acc (ctx, eqns) -> 
                  assert_msg (Context.equal ctx ctx2) "infer Match0";
                  acc @ eqns)
                eqns2 res
            in
            (ty', merge ctx1 ctx2, eqns1 @ eqns2 @ eqns))
        | None -> (
          let res = infer_cover cover id_ctx in
          match res with
          | [] -> failwith "infer Match2"
          | (t, ctx2, eqns2) :: res ->
            let eqns2 =
              List.fold_left
                (fun acc (t', ctx, eqns) ->
                  assert_msg (Context.equal ctx2 ctx)  
                    (asprintf "infer Match4(%a;@;<1 2>%a)"
                      Context.pp v_ctx Context.pp v_ctx);
                  (t, t') :: acc @ eqns)
                eqns2 res
            in
            (t, merge ctx1 ctx2, eqns1 @ eqns2 @ eqns)))
      | _ -> failwith "infer Match5")
    | Axiom (_, ty) ->
      let _, eqns = infer_sort v_ctx id_ctx ty in 
      (ty, VarMap.empty, eqns))

and check v_ctx id_ctx t ty =
  match t with
  | Meta _ -> (VarMap.empty, [])
  | Lambda b -> (
    let x, ub1 = unbind b in
    match whnf ty with
    | TyProd (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt, eqns1 = infer_sort v_ctx id_ctx ty in
      let ctx, eqns2 = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub1 ub2 in
      let ctx = remove x ctx srt in
      assert_msg (VarMap.is_empty ctx)
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@.%a@]" 
          Terms.pp t Terms.pp ty Context.pp' ctx); 
      (ctx, eqns1 @ eqns2)
    | LnProd (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt, eqns1 = infer_sort v_ctx id_ctx ty in
      let ctx, eqns2 = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub1 ub2 in
      (remove x ctx srt, eqns1 @ eqns2)
    | _ -> 
      failwith
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@]" 
          Terms.pp t Terms.pp ty))
  | Fix b ->
    let x, ub = unbind b in
    let srt, eqns1 = infer_sort v_ctx id_ctx ty in
    let ctx, eqns2 = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub ty in
    assert_msg (VarMap.is_empty ctx) "check Fix";
    (ctx, eqns1 @ eqns2)
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
    let ty', ctx, eqns = infer v_ctx id_ctx (LetIn (t, b)) in
    (ctx, (ty, ty') :: eqns)
  | DCons (id, ts) -> (
    match whnf ty with
    | TCons (_, ts') ->
      let DConstr (_, pscope) = find_dcons id id_ctx in
      let pscope =
        List.fold_left
          (fun pscope t ->
            match pscope with
            | PBind (ty, pb) -> subst pb (Ann (t, ty))
            | PBase _ -> pscope) pscope ts'
      in
      let ty', ctx, eqns = infer_pscope v_ctx id_ctx ts pscope in
      (ctx, (ty, ty') :: eqns)
    | _ ->
      let ty', ctx, eqns = infer v_ctx id_ctx t in
      (ctx, (ty, ty') :: eqns))
  | Match (t, mot, pbs) -> (
    match mot with
    | Some _ ->
      let ty', ctx, eqns = infer v_ctx id_ctx (Match (t, mot, pbs)) in
      (ctx, (ty, ty') :: eqns)
    | None ->
      let ty1, ctx1, eqns1 = infer v_ctx id_ctx t in
      let ty1 = whnf ty1 in
      match ty1 with
      | TCons (id, ts) -> (
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover = coverage v_ctx id_ctx pbs ds ts in
        let res = check_cover cover id_ctx ty in
        match res with
        | [] -> (ctx1, eqns1)
        | (ctx2, eqns2) :: res ->
          let eqns2 =
            List.fold_left
              (fun acc (ctx, eqns) ->
                assert_msg (Context.equal ctx2 ctx)  
                  (asprintf "infer Match4(%a;@;<1 2>%a)"
                    Context.pp v_ctx Context.pp v_ctx);
                acc @ eqns)
              eqns2 res
          in
          (merge ctx1 ctx2, eqns1 @ eqns2))
      | _ ->
        let ty', ctx, eqns = infer v_ctx id_ctx t in
        (ctx, (ty, ty') :: eqns))
  | _ ->
    let ty', ctx, eqns = infer v_ctx id_ctx t in
    (ctx, (ty, ty') :: eqns)

and infer_pscope v_ctx id_ctx ts pscope =
  match ts, pscope with
  | t :: ts, PBind (ty, pscope) ->
    let ctx1, eqns1 = check v_ctx id_ctx t ty in
    let ty, ctx2, eqns2 =
      infer_pscope v_ctx id_ctx ts (subst pscope (Ann (t, ty)))
    in
    (ty, merge ctx1 ctx2, eqns1 @ eqns2)
  | ts, PBase tscope -> infer_tscope v_ctx id_ctx ts tscope
  | _ ->
    failwith 
      (asprintf "infer_pscope(%a; %d)" 
        pp_pscope pscope (List.length ts))

and infer_tscope v_ctx id_ctx ts tscope =
  match ts, tscope with
  | t :: ts, TBind (ty, tscope) ->
    let ctx1, eqns1 = check v_ctx id_ctx t ty in
    let ty, ctx2, eqns2 = 
      infer_tscope v_ctx id_ctx ts (subst tscope (Ann (t, ty)))
    in
    (ty, merge ctx1 ctx2, eqns1 @ eqns2)
  | [], TBase ty -> (ty, VarMap.empty, [])
  | _ ->
    failwith 
      (asprintf "infer_tscope(%a; %d)" 
        pp_tscope tscope (List.length ts))

and coverage v_ctx id_ctx pbs ds ts =
  let rec strip = function
    | PVar x -> x
    | _ -> failwith "strip"
  and find id = function
    | (DConstr (id', _) as d) :: ds ->
      if Id.equal id id'
      then (d, ds)
      else
        let (d', ds') = find id ds in
        (d', d :: ds')
    | _ -> failwith "find"
  and t_of_p = function
    | PVar x -> Var x
    | PTCons (id, ps) ->
      TCons (id, List.map t_of_p ps)
    | PDCons (id, ps) ->
      DCons (id, List.map t_of_p ps)
  and arity_pscope v_ctx pscope ts xs =
    match pscope, ts with
    | PBind (ty, pscope), t :: ts ->
      let pscope = subst pscope (Ann (t, ty)) in
      let v_ctx, ty, xsrt, eqns = arity_pscope v_ctx pscope ts xs in
      (v_ctx, ty, xsrt, eqns)
    | PBase tscope, _ -> arity_tscope v_ctx tscope xs
    | _ -> failwith "arity_pscope"
  and arity_tscope v_ctx tscope xs = 
    match tscope, xs with
    | TBind (ty, tscope), x :: xs ->
      let srt, eqns1 = infer_sort v_ctx id_ctx ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      let tscope = subst tscope (Var x) in
      let v_ctx, ty, xsrt, eqns2 = arity_tscope v_ctx tscope xs in
      (v_ctx, ty, (x, srt) :: xsrt, eqns1 @ eqns2)
    | TBase ty, [] -> (v_ctx, ty, [], [])
    | _ -> failwith "arity_tscope"
  in
  match pbs with
  | pb :: pbs -> (
    let p, ub = unbind_p pb in
    match p with
    | PDCons (id, ps) ->
      let xs = List.map strip ps in
      let t = t_of_p p in
      let DConstr (_, pscope), ds = find id ds in
      let v_ctx, ty, xsrt, eqns = arity_pscope v_ctx pscope ts xs in
      let ds = coverage v_ctx id_ctx pbs ds ts in
      (v_ctx, t, ty, ub, xsrt, eqns) :: ds
    | _ -> failwith "coverage")
  | [] -> (
    match ds with
    | [] -> []
    | _ -> failwith "coverage")

and infer_cover cover id_ctx =
  match cover with
  | (v_ctx, _, _, b, xsrt, eqns1) :: cover ->
    let ty, ctx, eqns2 = infer v_ctx id_ctx b in
    let ctx =
      List.fold_left
        (fun ctx (x, srt) -> remove x ctx srt)
      ctx xsrt
    in
    (ty, ctx, eqns1 @ eqns2) :: infer_cover cover id_ctx
  | _ -> []

and check_cover cover id_ctx ty =
  match cover with
  | (v_ctx, _, _, b, xsrt, eqns1) :: cover ->
    let ctx, eqns2 = check v_ctx id_ctx b ty in
    let ctx =
      List.fold_left
        (fun ctx (x, srt) -> remove x ctx srt)
      ctx xsrt
    in
    (ctx, eqns1 @ eqns2) :: check_cover cover id_ctx ty
  | _ -> []

and check_motive cover id_ctx mot srt =
  match cover with
  | (v_ctx, t, ty, b, xsrt, eqns1) :: cover ->
    let mot' =
      if srt = Type then subst mot t
      else (
        assert_msg (not (binder_occur mot)) "check_motive";
        snd (unbind mot))
    in
    let mot' = subst_p mot' ty in
    let ctx, eqns2 = check v_ctx id_ctx b mot' in
    let ctx = 
      List.fold_left
        (fun ctx (x, srt) -> remove x ctx srt)
      ctx xsrt
    in
    (ctx, eqns1 @ eqns2) :: check_motive cover id_ctx mot srt
  | _ -> []

let rec elab_top v_ctx id_ctx mmap top =
  match top with
  | Empty -> (VarMap.empty, id_ctx, mmap)
  | Define (t, top) ->
    let ty1, ctx1, eqns1 = infer v_ctx id_ctx t in
    let srt, eqns2 = infer_sort v_ctx id_ctx ty1 in
    let mmap = unify mmap (eqns1 @ eqns2) in
    let t = resolve mmap t in
    let ty1 = resolve mmap ty1 in
    let ctx2, id_ctx, mmap =
      if srt = Type && VarMap.is_empty ctx1 then
        elab_top v_ctx id_ctx mmap (subst top t)
      else
        let x, top = unbind top in
        let ctx, id_ctx, mmap =
          elab_top (VarMap.add x (ty1, srt) v_ctx)  id_ctx mmap top
        in
        (remove x ctx srt, id_ctx, mmap)
    in
    (merge ctx1 ctx2, id_ctx, mmap)
  | Datype (tcs, top) -> (
    let TConstr (id, pscope, dcs) = tcs in
    let eqns = check_pscope v_ctx id_ctx pscope Type in
    let mmap = unify mmap eqns in
    let pscope = unbox (resolve_pscope mmap pscope) in
    let id_ctx = IdMap.add id (TConstr (id, pscope, [])) id_ctx in
    let eqns =
      List.fold_left
        (fun acc (DConstr (_, pscope)) ->
          let eqns = check_pscope v_ctx id_ctx pscope Type in
          param_pscope pscope id [];
          (acc @ eqns))
        eqns dcs
    in
    let mmap = unify mmap eqns in
    let dcs = List.map (fun x -> unbox (resolve_dcons mmap x)) dcs in
    let id_ctx = IdMap.add id (TConstr (id, pscope, dcs)) id_ctx in
    elab_top v_ctx id_ctx mmap top)

and check_pscope v_ctx id_ctx pscope srt =
  match pscope with
  | PBase tscope -> check_tscope v_ctx id_ctx tscope srt
  | PBind (t, pscope) ->
    let x, pscope = unbind pscope in
    let srt', eqns1 = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, srt) v_ctx in
    let eqns2 = check_pscope v_ctx id_ctx pscope (min_sort srt srt') in
    eqns1 @ eqns2

and check_tscope v_ctx id_ctx tscope srt =
  match tscope with
  | TBase t ->
    let srt', eqns = infer_sort v_ctx id_ctx t in
    assert_msg (cmp_sort srt' srt)
      (asprintf "check_tscope(srt := %a; srt' :=%a)" pp_s srt pp_s srt');
    eqns
  | TBind (t, tscope) ->
    let x, tscope = unbind tscope in
    let srt', eqns1 = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, srt') v_ctx in
    let eqns2 = check_tscope v_ctx id_ctx tscope (min srt srt') in
    eqns1 @ eqns2

and param_pscope pscope id xs =
  match pscope with
  | PBase tscope ->
    param_tscope tscope id (List.rev xs)
  | PBind (_, pscope) ->
    let x, pscope = unbind pscope in
    param_pscope pscope id (x :: xs)

and param_tscope tscope id xs =
  let rec param xs ts =
    match xs, ts with
    | [], _ -> ()
    | x :: xs, Var t :: ts ->
      assert_msg (eq_vars x t)
        (asprintf "param_tscope(%a; %a" pp_v x pp_v t);
      param xs ts
    | x :: _, t :: _ ->
      failwith (asprintf "param_tscope(%a; %a)" pp_v x Terms.pp t)
    | x :: _, [] ->
      failwith (asprintf "param_tscope(%a; ??)" pp_v x)
  in
  match tscope with
  | TBase ty -> (
    match ty with
    | TCons (id', ts) ->
      assert_msg (Id.equal id id')
        (asprintf "param_tscope(%a)" Terms.pp ty);
      param xs ts
    | _ ->
      failwith
        (asprintf "param_tscope(%a)" Terms.pp ty))
  | TBind (_, tscope) ->
    let _, tscope = unbind tscope in
    param_tscope tscope id xs

let elab top =
  let _, _, mmap = elab_top VarMap.empty IdMap.empty MetaMap.empty top in
  mmap