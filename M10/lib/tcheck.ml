open Bindlib
open Format
open Util
open Names
open Terms
open Context
open Equality

let cmp_sort t1 t2 =
  match t1, t2 with
  | Type, Linear -> false
  | _ -> true

let min_sort t1 t2 = 
  match t1 with
  | Type -> t2
  | Linear -> t1

let rec infer_sort v_ctx id_ctx ty =
  let t, ctx = infer v_ctx id_ctx ty in
  match whnf t with
  | Sort t -> 
    assert_msg (VarMap.is_empty ctx) "non-clean context for sort"; t
  | _ ->
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp t)

and infer v_ctx id_ctx t =
  match t with
  | Var x -> (
    let ty, srt = 
      try find x v_ctx 
      with e -> 
        printf "%a" Context.pp v_ctx; raise e
    in
    match srt with
    | Type -> (ty, VarMap.empty)
    | Linear -> (ty, VarMap.singleton x ty))
  | Meta _ -> failwith "infer Meta"
  | Ann (t, ty) -> (
    match t with
    | LetIn (t, b) ->
      let x, ub = unbind b in
      let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
      let ctx = check v_ctx id_ctx (LetIn (t, b)) ty in
      (ty, ctx)
    | _ ->
      let ctx = check v_ctx id_ctx t ty in
      (ty, ctx))
  | Sort srt -> (
    match srt with
    | Type -> (Sort Type, VarMap.empty)
    | Linear -> (Sort Type, VarMap.empty))
  | TyProd (ty, b) ->
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let _ = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
    (Sort Type, VarMap.empty)
  | LnProd (ty, b) ->
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let srt = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
    assert_msg (srt = Linear) "infer LnProd";
    (Sort Linear, VarMap.empty)
  | Lambda _ -> failwith (asprintf "infer Lambda(%a)" Terms.pp t)
  | Fix _ -> failwith (asprintf "infer Fix(%a)" Terms.pp t)
  | App (t1, t2) -> (
    let ty1, ctx1 = infer v_ctx id_ctx t1 in
    match whnf ty1 with
    | TyProd (ty, b) ->
      let ctx2 = check v_ctx id_ctx t2 ty in
      (subst b t2, merge ctx1 ctx2)
    | LnProd (ty, b) ->
      let ctx2 = check v_ctx id_ctx t2 ty in
      (subst b t2, merge ctx1 ctx2)
    | _ -> failwith (asprintf "@[infer App(t :=@;<1 2>%a)@]" Terms.pp t))
  | LetIn (t, b) -> (
    let ty1, ctx1 = infer v_ctx id_ctx t in
    let srt = infer_sort v_ctx id_ctx ty1 in
    let ty2, ctx2 =
      if srt = Type && VarMap.is_empty ctx1 then
        infer v_ctx id_ctx (subst b t)
      else
        let x, ub = unbind b in
        let ty2, ctx2 = 
          infer (VarMap.add x (ty1, srt) v_ctx) id_ctx ub
        in
        (ty2, remove x ctx2 srt)
    in
    (ty2, merge ctx1 ctx2))
  | TCons (id, ts) ->
    let TConstr (_, pscope, _) = IdMap.find id id_ctx in
    infer_pscope v_ctx id_ctx ts pscope
  | DCons (id, ts) -> (
    match find_dcons id id_ctx with
    | DConstr (_, PBase tscope) ->
      infer_tscope v_ctx id_ctx ts tscope
    | _ -> failwith (asprintf "infer DCons(%a)" Terms.pp t))
  | Match (t, mot, pbs) -> (
    let ty, ctx1 = infer v_ctx id_ctx t in
    let srt = infer_sort v_ctx id_ctx ty in
    let ty = whnf ty in
    match ty with
    | TCons (id, ts) -> (
      let TConstr (_, _, ds) = IdMap.find id id_ctx in
      let cover = coverage v_ctx id_ctx pbs ds ts in
      match mot with
      | Some mot -> (
        let ty' = subst_p (subst mot t) ty in
        let ctxs = check_motive cover id_ctx mot srt in
        match ctxs with
        | [] -> (ty', ctx1)
        | ctx2 :: ctxs ->
          List.iter
            (fun ctx ->
              assert_msg (Context.equal ctx2 ctx)  "infer Match0") ctxs;
          (ty', merge ctx1 ctx2))
      | None -> (
        let ctxs = infer_cover cover id_ctx in
        match ctxs with
        | [] -> failwith "infer Match2"
        | (t, ctx2) :: ctxs ->
          List.iter
            (fun (t', ctx) ->
              assert_msg (equal t t')  
                (asprintf "infer Match3(%a;@;<1 2>%a)"
                  Terms.pp t Terms.pp t');
              assert_msg (Context.equal ctx2 ctx)  
                (asprintf "infer Match4(%a;@;<1 2>%a)"
                  Context.pp v_ctx Context.pp v_ctx)) ctxs;
          (t, merge ctx1 ctx2)))
    | _ -> failwith "infer Match5")
  | Axiom (_, ty) ->
    let _ = infer_sort v_ctx id_ctx ty in
    (ty, VarMap.empty)

and check v_ctx id_ctx t ty =
  match t with
  | Meta _ -> failwith "check Meta"
  | Lambda b -> (
    let x, ub1 = unbind b in
    match whnf ty with
    | TyProd (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt = infer_sort v_ctx id_ctx ty in
      let ctx = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub1 ub2 in
      let ctx = remove x ctx srt in
      assert_msg (VarMap.is_empty ctx) 
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@.%a@]" 
          Terms.pp t Terms.pp ty Context.pp' ctx); ctx
    | LnProd (ty, b2) ->
      let ub2 = subst b2 (Var x) in
      let srt = infer_sort v_ctx id_ctx ty in
      let ctx = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub1 ub2 in
      remove x ctx srt
    | _ -> 
      failwith
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@]" 
          Terms.pp t Terms.pp ty))
  | Fix b ->
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let ctx = check (VarMap.add x (ty, srt) v_ctx) id_ctx ub ty in
    assert_msg (VarMap.is_empty ctx) "check Fix"; ctx
  | LetIn (t, b) ->
    let x, ub = unbind b in
    let b = unbox (bind_var x (lift (Ann (ub, ty)))) in
    let ty', ctx = infer v_ctx id_ctx (LetIn (t, b)) in
    assert_msg (equal ty ty')
      (asprintf "check LetIn(ty := %a; ty' := %a)" 
        Terms.pp ty Terms.pp ty');
    ctx
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
      let ty', ctx = infer_pscope v_ctx id_ctx ts pscope in
      assert_msg (equal ty ty') 
        (asprintf "check DCons(@[expected := %a;@;<1 0>actual   := %a@])"
          Terms.pp (whnf ty) Terms.pp (whnf ty'));
      ctx
    | _ -> 
      let ty', ctx = infer v_ctx id_ctx t in
      assert_msg (equal ty ty')
        (asprintf "check DCons(@[expected := %a;@;<1 0>actual   := %a@])" 
          Terms.pp (nf ty) Terms.pp (nf ty')); ctx)
  | Match (t, opt, pbs) -> (
    match opt with
    | Some _ ->
      let ty', ctx = infer v_ctx id_ctx (Match (t, opt, pbs)) in
      assert_msg (equal ty ty')
        (asprintf "check Match(ty := %a; ty' := %a)" 
          Terms.pp ty Terms.pp ty');
      ctx
    | _ ->
      let ty1, ctx1 = infer v_ctx id_ctx t in
      let ty1 = whnf ty1 in
      match ty1 with
      | TCons (id, ts) -> (
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover = coverage v_ctx id_ctx pbs ds ts in
        let ctxs = check_cover cover id_ctx ty in
        match ctxs with
        | [] -> ctx1
        | ctx2 :: ctxs ->
          List.iter
            (fun ctx ->
              assert_msg (Context.equal ctx2 ctx)  
                "uneven Match context") ctxs;
            (merge ctx1 ctx2))
      | _ -> failwith "check Match2")
  | _ ->
    let ty', ctx = infer v_ctx id_ctx t in
    assert_msg (equal ty ty')
      (asprintf "check (@[expected := %a;@;<1 0>actual   := %a@])" 
        Terms.pp (nf ty) Terms.pp (nf ty')); ctx

and infer_pscope v_ctx id_ctx ts pscope =
  match ts, pscope with
  | t :: ts, PBind (ty, pscope) ->
    let ctx1 = check v_ctx id_ctx t ty in
    let ty, ctx2 =
      infer_pscope v_ctx id_ctx ts (subst pscope (Ann (t, ty)))
    in
    (ty, merge ctx1 ctx2)
  | ts, PBase tscope -> infer_tscope v_ctx id_ctx ts tscope
  | _ ->
    failwith 
      (asprintf "infer_pscope(%a; %d)" 
        pp_pscope pscope (List.length ts))

and infer_tscope v_ctx id_ctx ts tscope =
  match ts, tscope with
  | t :: ts, TBind (ty, tscope) ->
    let ctx1 = check v_ctx id_ctx t ty in
    let ty, ctx2 = 
      infer_tscope v_ctx id_ctx ts (subst tscope (Ann (t, ty)))
    in
    (ty, merge ctx1 ctx2)
  | [], TBase ty -> (ty, VarMap.empty)
  | _ ->  failwith "infer_tscope"

and t_of_p = function
  | PVar x -> Var x
  | PTCons (id, ps) ->
    TCons (id, List.map t_of_p ps)
  | PDCons (id, ps) ->
    DCons (id, List.map t_of_p ps)

and coverage v_ctx id_ctx pbs ds ts =
  let strip = function
    | PVar x -> x
    | _ -> failwith "strip"
  in
  let rec find id = function
    | (DConstr (id', _) as d) :: ds ->
      if Id.equal id id'
      then (d, ds)
      else
        let (d', ds') = find id ds in
        (d', d :: ds')
    | _ -> failwith "find"
  in
  let rec arity_pscope v_ctx pscope ts xs =
    match pscope, ts with
    | PBind (ty, pscope), t :: ts ->
      let pscope = subst pscope (Ann (t, ty)) in
      let v_ctx, ty, xsrt = arity_pscope v_ctx pscope ts xs in
      (v_ctx, ty, xsrt)
    | PBase tscope, _ -> arity_tscope v_ctx tscope xs
    | _ -> failwith "arity_pscope"
  and arity_tscope v_ctx tscope xs = 
    match tscope, xs with
    | TBind (ty, tscope), x :: xs ->
      let srt = infer_sort v_ctx id_ctx ty in
      let v_ctx = VarMap.add x (ty, srt) v_ctx in
      let tscope = subst tscope (Var x) in
      let v_ctx, ty, xsrt = arity_tscope v_ctx tscope xs in
      (v_ctx, ty, (x, srt) :: xsrt)
    | TBase ty, [] -> (v_ctx, ty, [])
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
      let v_ctx, ty, xsrt = arity_pscope v_ctx pscope ts xs in
      let ds = coverage v_ctx id_ctx pbs ds ts in
      (v_ctx, t, ty, ub, xsrt) :: ds
    | _ -> failwith "coverage")
  | [] -> (
    match ds with
    | [] -> []
    | _ -> failwith "coverage")

and infer_cover cover id_ctx =
  match cover with
  | (v_ctx, _, _, b, xsrt) :: cover ->
    let ty, ctx = infer v_ctx id_ctx b in
    let ctx =
      List.fold_left
        (fun ctx (x, srt) -> remove x ctx srt)
      ctx xsrt
    in
    (ty, ctx) :: infer_cover cover id_ctx
  | _ -> []

and check_cover cover id_ctx ty =
  match cover with
  | (v_ctx, _, _, b, xsrt) :: cover ->
    let ctx = check v_ctx id_ctx b ty in
    let ctx =
      List.fold_left
        (fun ctx (x, srt) -> remove x ctx srt)
      ctx xsrt
    in
    ctx :: check_cover cover id_ctx ty
  | _ -> []

and check_motive cover id_ctx mot srt =
  match cover with
  | (v_ctx, t, ty, b, xsrt) :: cover ->
    let mot' =
      if srt = Type then subst mot t
      else (
        assert_msg (not (binder_occur mot)) "check_motive";
        snd (unbind mot))
    in
    let mot' = subst_p mot' ty in
    let ctx = check v_ctx id_ctx b mot' in
    let ctx =
      List.fold_left
        (fun ctx (x, srt) -> remove x ctx srt)
      ctx xsrt
    in
    ctx :: check_motive cover id_ctx mot srt
  | _ -> []

let rec infer_top v_ctx id_ctx top =
  match top with
  | Empty -> (VarMap.empty, id_ctx)
  | Define (t, top) ->
    let ty1, ctx1 = infer v_ctx id_ctx t in
    let srt = infer_sort v_ctx id_ctx ty1 in
    let ctx2, id_ctx =
      if srt = Type && VarMap.is_empty ctx1 then
        let x, _ = unbind top in
        let v_ctx = VarMap.add x (ty1, srt) v_ctx in
        infer_top v_ctx id_ctx (subst top t)
      else
        let x, top = unbind top in
        let ctx, id_ctx = 
          infer_top (VarMap.add x (ty1, srt) v_ctx) id_ctx top
        in
        (remove x ctx srt, id_ctx)
    in
    (merge ctx1 ctx2, id_ctx)
  | Datype (tcs, top) -> (
    match tcs with
    | TConstr (id, pscope, dcs) ->
      check_pscope v_ctx id_ctx pscope Type;
      let id_ctx = IdMap.add id (TConstr (id, pscope, [])) id_ctx in
      List.iter
        (fun (DConstr (_, pscope)) ->
          check_pscope v_ctx id_ctx pscope Type;
          param_pscope pscope id []) dcs;
      let id_ctx = IdMap.add id (TConstr (id, pscope, dcs)) id_ctx in
      infer_top v_ctx id_ctx top)
        
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

and check_pscope v_ctx id_ctx pscope srt =
  match pscope with
  | PBase tscope -> check_tscope v_ctx id_ctx tscope srt
  | PBind (t, pscope) ->
    let x, pscope = unbind pscope in
    let srt' = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, srt) v_ctx in
    check_pscope v_ctx id_ctx pscope (min_sort srt srt')

and check_tscope v_ctx id_ctx tscope srt =
  match tscope with
  | TBase t ->
    let srt' = infer_sort v_ctx id_ctx t in
    assert_msg (cmp_sort srt' srt)
      (asprintf "check_tscope(srt := %a; srt' :=%a)" pp_s srt pp_s srt');
  | TBind (t, tscope) ->
    let x, tscope = unbind tscope in
    let srt' = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, srt') v_ctx in
    check_tscope v_ctx id_ctx tscope (min srt srt')

let infer top = 
  let ctx, _ = infer_top VarMap.empty IdMap.empty top in
  assert_msg (VarMap.is_empty ctx) "non-clean context"