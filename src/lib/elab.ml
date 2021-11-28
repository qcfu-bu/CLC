open Bindlib
open Format
open Util
open Names
open Terms
open Context
open Equality
open Unify

let cmp_sort t1 t2 =
  match t1, t2 with
  | U, L -> false
  | _ -> true

let min_sort t1 t2 = 
  match t1 with
  | U -> t2
  | L -> t1

let rec infer_sort v_ctx id_ctx eqns mmap ty =
  let srt, eqns, mmap = infer v_ctx id_ctx eqns mmap ty in
  match whnf srt with
  | Sort srt -> (srt, eqns, mmap)
  | _ ->
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp srt)

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
      let ty, srt = find x v_ctx in
      match srt with
      | U -> (ty, eqns, mmap)
      | L -> (ty, eqns, mmap))
    | Meta _ -> failwith "infer Meta"
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
      let _, eqns, mmap = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub in
      (Sort U, eqns, mmap)
    | Lolli (ty, b) ->
      let x, ub = unbind b in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let _, eqns, mmap = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub in
      (Sort L, eqns, mmap)
    | Lambda _ -> failwith (asprintf "infer Lambda(%a)" Terms.pp t)
    | Fix _ -> failwith (asprintf "infer Fix(%a)" Terms.pp t)
    | App (t1, t2) -> (
      let ty1, eqns, mmap = infer v_ctx id_ctx eqns mmap t1 in
      match whnf ty1 with
      | Arrow (ty, b) ->
        let eqns, mmap = check v_ctx id_ctx eqns mmap t2 ty in
        (subst b t2, eqns, mmap)
      | Lolli (ty, b) ->
        let eqns, mmap = check v_ctx id_ctx eqns mmap t2 ty in
        (subst b t2, eqns, mmap)
      | _ -> failwith (asprintf "@[infer App(t :=@;<1 2>%a)@]" Terms.pp t))
    | LetIn (t, b) -> (
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
      (ty2, eqns, mmap))
    | TCons (id, ts) -> (
      let TConstr (_, pscope, _) = IdMap.find id id_ctx in
      infer_pscope v_ctx id_ctx eqns mmap ts pscope)
    | DCons (id, ts) -> (
      match find_dcons id id_ctx with
      | DConstr (_, PBase tscope) ->
        infer_tscope v_ctx id_ctx eqns mmap ts tscope
      | _ -> failwith (asprintf "infer DCons(%a)" Terms.pp t))
    | Match (t, mot, pbs) -> (
      let ty, eqns, mmap  = infer v_ctx id_ctx eqns mmap t in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let ty = whnf ty in
      match ty with
      | TCons (id, ts) -> (
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover, eqns, mmap = coverage v_ctx id_ctx eqns mmap pbs ds ts in
        match mot with
        | Some mot -> (
          let ty' = subst_p (subst mot t) ty in
          let eqns, mmap = check_motive cover id_ctx eqns mmap mot srt in
          (ty', eqns, mmap))
        | None -> (
          let ts, eqns, mmap = infer_cover cover id_ctx eqns mmap in
          match ts with
          | [] -> failwith "infer Match2"
          | t :: ts ->
            let eqns =
              List.fold_left (fun acc t' -> (t, t') :: acc) eqns ts
            in
            (t, eqns, mmap)))
      | _ -> failwith "infer Match5")
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
      check (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub1 ub2
    | Lolli (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      check (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub1 ub2
    | _ -> failwith "check Lambda")
  | Fix b ->
    let x, ub = unbind b in
    let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
    check (VarMap.add x (ty, srt) v_ctx) id_ctx eqns mmap ub ty
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
    let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap (LetIn (t, b)) in
    ((ty, ty') :: eqns, mmap)
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
      let ty', eqns, mmap = infer_pscope v_ctx id_ctx eqns mmap ts pscope in
      ((ty, ty') :: eqns, mmap)
    | _ ->
      let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap t in
      ((ty, ty') :: eqns), mmap)
  | Match (t, mot, pbs) -> (
    match mot with
    | Some _ ->
      let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap (Match (t, mot, pbs)) in
      ((ty, ty') :: eqns, mmap)
    | None ->
      let ty1, eqns, mmap = infer v_ctx id_ctx eqns mmap t in
      let ty1 = whnf ty1 in
      match ty1 with
      | TCons (id, ts) ->
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover, eqns, mmap = coverage v_ctx id_ctx eqns mmap pbs ds ts in
        check_cover cover id_ctx eqns mmap ty
      | _ -> failwith "check Match")
  | _ ->
    let ty', eqns, mmap = infer v_ctx id_ctx eqns mmap t in
    ((ty, ty') :: eqns, mmap)

and infer_pscope v_ctx id_ctx eqns mmap ts pscope =
  match ts, pscope with
  | t :: ts, PBind (ty, pscope) ->
    let eqns, mmap = check v_ctx id_ctx eqns mmap t ty in
    infer_pscope v_ctx id_ctx eqns mmap ts (subst pscope (Ann (t, ty)))
  | ts, PBase tscope -> 
    infer_tscope v_ctx id_ctx eqns mmap ts tscope
  | _ ->
    failwith 
      (asprintf "infer_pscope(%a; %d)" 
        pp_pscope pscope (List.length ts))

and infer_tscope v_ctx id_ctx eqns mmap ts tscope =
  match ts, tscope with
  | t :: ts, TBind (ty, tscope) ->
    let eqns, mmap = check v_ctx id_ctx eqns mmap t ty in
    infer_tscope v_ctx id_ctx eqns mmap ts (subst tscope (Ann (t, ty)))
  | [], TBase ty -> (ty, eqns, mmap)
  | _ ->
    failwith 
      (asprintf "infer_tscope(%a; %d)" 
        pp_tscope tscope (List.length ts))

and coverage v_ctx id_ctx eqns mmap pbs ds ts =
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
  and arity_pscope v_ctx eqns mmap pscope ts xs =
    match pscope, ts with
    | PBind (ty, pscope), t :: ts ->
      let pscope = subst pscope (Ann (t, ty)) in
      arity_pscope v_ctx eqns mmap pscope ts xs
    | PBase tscope, _ -> arity_tscope v_ctx eqns mmap tscope xs
    | _ -> failwith "arity_pscope"
  and arity_tscope v_ctx eqns mmap tscope xs = 
    match tscope, xs with
    | TBind (ty, tscope), x :: xs ->
      let srt, eqns, mmap = infer_sort v_ctx id_ctx eqns mmap ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      let tscope = subst tscope (Var x) in
      let v_ctx, ty, xsrt, eqns, mmap = arity_tscope v_ctx eqns mmap tscope xs in
      (v_ctx, ty, (x, srt) :: xsrt, eqns, mmap)
    | TBase ty, [] -> (v_ctx, ty, [], eqns, mmap)
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
      let v_ctx, ty, xsrt, eqns, mmap = arity_pscope v_ctx eqns mmap pscope ts xs in
      let ds, eqns, mmap = coverage v_ctx id_ctx eqns mmap pbs ds ts in
      ((v_ctx, t, ty, ub, xsrt) :: ds, eqns, mmap)
    | _ -> failwith "coverage")
  | [] -> (
    match ds with
    | [] -> ([], eqns, mmap)
    | _ -> failwith "coverage")

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
  match cover with
  | (v_ctx, t, ty, b, _) :: cover ->
    let mot' =
      if srt = U then subst mot t
      else (
        assert_msg (not (binder_occur mot)) "check_motive";
        snd (unbind mot))
    in
    let mot' = subst_p mot' ty in
    let eqns, mmap = check v_ctx id_ctx eqns mmap b mot' in
    check_motive cover id_ctx eqns mmap mot srt
  | _ -> (eqns, mmap)

let rec elab_top v_ctx id_ctx eqns mmap top =
  match top with
  | Empty -> (id_ctx, mmap)
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
  | Datype (tcs, top) -> (
    let TConstr (id, pscope, dcs) = tcs in
    let eqns, mmap = check_pscope v_ctx id_ctx eqns mmap pscope U in
    let mmap = unify mmap eqns in
    let pscope = unbox (resolve_pscope mmap pscope) in
    let id_ctx = IdMap.add id (TConstr (id, pscope, [])) id_ctx in
    let eqns, mmap =
      List.fold_left
        (fun (eqns, mmap) (DConstr (_, pscope)) ->
          let eqns, mmap = check_pscope v_ctx id_ctx eqns mmap pscope U in
          param_pscope pscope id [];
          (eqns, mmap))
        (eqns, mmap) dcs
    in
    let mmap = unify mmap eqns in
    let dcs = List.map (fun x -> unbox (resolve_dcons mmap x)) dcs in
    let id_ctx = IdMap.add id (TConstr (id, pscope, dcs)) id_ctx in
    elab_top v_ctx id_ctx eqns mmap top)

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
    assert_msg (cmp_sort srt' srt)
      (asprintf "check_tscope(srt := %a; srt' :=%a)" pp_s srt pp_s srt');
    (eqns, mmap)
  | TBind (t, tscope) ->
    let x, tscope = unbind tscope in
    let srt', eqns, mmap = infer_sort v_ctx id_ctx eqns mmap t in
    let v_ctx = VarMap.add x (t, srt') v_ctx in
    check_tscope v_ctx id_ctx eqns mmap tscope (min srt srt')

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
  let _, mmap = 
    elab_top VarMap.empty IdMap.empty [] MetaMap.empty top 
  in
  mmap