open Bindlib
open Format
open Names
open Terms
open Context
open Equality

let assert_msg cond msg =
  if cond then ()
  else (prerr_endline msg; assert false)

let rec infer_sort v_ctx id_ctx ty =
  let sort, v_ctx = infer v_ctx id_ctx ty in
  match whnf sort with
  | Type   -> (Ty, v_ctx)
  | Linear -> (Ln, v_ctx)
  | sort   ->
    failwith
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp sort)

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
    | (DConstr (id0, _) as d) :: ds ->
      if Id.equal id id0 
      then (d, ds)
      else
        let (d0, ds0) = find id ds in
        (d0, d :: ds0)
    | _ -> failwith "find"
  in
  let rec arity_pscope v_ctx pscope ts xs =
    match pscope, ts with
    | PBind (ty, pscope), t :: ts ->
      let pscope = subst pscope (Ann (t, ty)) in
      arity_pscope v_ctx pscope ts xs
    | PBase tscope, _ ->
      arity_tscope v_ctx tscope xs
    | _ -> failwith "arity_pscope"
  and arity_tscope v_ctx tscope xs =
    match tscope, xs with
    | TBind (ty, tscope), x :: xs ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx = add x (ty, m) v_ctx in
      let tscope = subst tscope (Var x) in
      let ctx, ty, xm = arity_tscope v_ctx tscope xs in
      (ctx, ty, (x, m) :: xm)
    | TBase ty, [] -> (empty, ty, [])
    | _ -> failwith "arity_tscope"
  in
  match pbs with
  | pb :: pbs -> (
    let p, b = unbind_p pb in
    match p with
    | PDCons (id, ps) ->
      let xs = List.map strip ps in
      let t = t_of_p p in
      let DConstr (_, pscope), ds = find id ds in
      let ctx, ty, xm = arity_pscope v_ctx pscope ts xs in
      let cover = coverage v_ctx id_ctx pbs ds ts in
      (ctx, t, ty, b, xm) :: cover
    | _ -> failwith "coverage")
  | [] -> (
    match ds with
    | [] -> []
    | _ -> failwith "coverage")

and infer v_ctx id_ctx t =
  match t with
  | Var x -> (
    match find x v_ctx with
    | (ty, Ty) -> (ty, empty)
    | (ty, Ln) -> (ty, singleton x ty))
  | Ann (t, ty) -> (
    match t with
    | LetIn (t, b) ->
      let x, b = unbind b in
      let b = unbox (bind_var x (lift (Ann (b, ty)))) in
      let ctx = check v_ctx id_ctx (LetIn (t, b)) ty in
      (ty, ctx)
    | _ ->
      let ctx = check v_ctx id_ctx t ty in
      (ty, ctx))
  | Type -> (Type, empty)
  | Linear -> (Type, empty)
  | TyProd (ty, b) ->
    let x, b = unbind b in
    let m, ctx1 = infer_sort v_ctx id_ctx ty in
    let _, ctx2 = infer_sort (add x (ty, m) v_ctx) id_ctx b in
    let ctx2 = remove x ctx2 m in
    (Type, merge ctx1 ctx2)
  | LnProd (ty, b) ->
    let x, b = unbind b in
    let m, ctx1 = infer_sort v_ctx id_ctx ty in
    let _, ctx2 = infer_sort (add x (ty, m) v_ctx) id_ctx b in
    let ctx2 = remove x ctx2 m in
    (Type, merge ctx1 ctx2)
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
  | LetIn (t, b) ->
    let ty1, ctx1 = infer v_ctx id_ctx t in
    let m, _ = infer_sort v_ctx id_ctx ty1 in
    let ty2, ctx2 =
      if m = Ty && is_empty ctx1 then
        infer v_ctx id_ctx (subst b t)
      else
        let x, b = unbind b in
        let ty2, ctx2 =
          infer (add x (ty1, m) v_ctx) id_ctx b
        in
        let ctx2 = remove x ctx2 m in
        (ty2, ctx2)
    in
    (ty2, merge ctx1 ctx2)
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
    let m, _ = infer_sort v_ctx id_ctx ty in
    let ty = whnf ty in
    match ty with
    | TCons (id, ts) -> (
      let TConstr (_, _, ds) = IdMap.find id id_ctx in
      let cover = coverage v_ctx id_ctx pbs ds ts in
      match mot with
      | Some mot -> (
        let ty = subst_p (subst mot t) ty in
        let ctxs = check_motive cover id_ctx mot m in
        match ctxs with
        | [] -> (ty, empty)
        | ctx :: ctxs ->
          List.iter (fun ctx0 -> 
            assert_msg (Context.equal ctx ctx0) "infer Match0") ctxs;
          (ty, merge ctx1 ctx))
      | _ -> (
        let ctxs = infer_cover cover id_ctx in
        match ctxs with
        | [] -> failwith "infer Match"
        | (t, ctx) :: ctxs ->
          List.iter (fun (t0, ctx0) -> 
            assert_msg (equal t t0)
              (asprintf "infer Match3(%a;@;<1 2>%a)"
                Terms.pp t Terms.pp t0);
            assert_msg (Context.equal ctx ctx0)
              (asprintf "infer Match4(%a;@;<1 2>%a)"
                Context.pp v_ctx Context.pp v_ctx)) ctxs;
          (t, merge ctx1 ctx)))
    | _ -> failwith "infer Match for non-inductive type")
  | Axiom (_, ty) ->
    let _ = infer_sort v_ctx id_ctx ty in
    (ty, empty)

and infer_pscope v_ctx id_ctx ts pscope =
  match ts, pscope with
  | t :: ts, PBind (ty, pscope) ->
    let ctx1 = check v_ctx id_ctx t ty in
    let ty, ctx2 = 
      infer_pscope v_ctx id_ctx ts (subst pscope (Ann (t, ty)))
    in
    (ty, merge ctx1 ctx2)
  | ts, PBase pscope -> infer_tscope v_ctx id_ctx ts pscope
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
  | _ -> 
    failwith 
      (asprintf "infer_tscope(%a; %d)" 
        pp_tscope tscope (List.length ts))

and infer_cover cover id_ctx = 
  match cover with
  | (v_ctx, _, _, b, xm) :: cover ->
    let ty, ctx = infer v_ctx id_ctx b in
    let ctx =
      List.fold_left (fun ctx (x, m) ->
        remove x ctx m) ctx xm
    in
    (ty, ctx) :: infer_cover cover id_ctx
  | _ -> []

and check v_ctx id_ctx t ty =
  let m, _ = infer_sort v_ctx id_ctx ty in
  match t with
  | Lambda b -> (
    match whnf ty with
    | TyProd (ty, b0) ->
      let x, b, b0 = unbind2 b b0 in
      let m, _ = infer_sort v_ctx id_ctx ty in
      let ctx = 
        check (add x (ty, m) (pure v_ctx)) id_ctx b b0
      in
      remove x ctx m
    | LnProd (ty, b0) ->
      let x, b, b0 = unbind2 b b0 in
      let m, _ = infer_sort v_ctx id_ctx ty in
      let ctx = 
        check (add x (ty, m) v_ctx) id_ctx b b0
      in
      remove x ctx m
    | _ -> 
      failwith
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@]" 
          Terms.pp t Terms.pp ty))
  | Fix b ->
    let x, b = unbind b in
    let ctx = 
      check (pure (add x (ty, m) v_ctx)) id_ctx b ty
    in
    remove x ctx m
  | LetIn (t, b) ->
    let x, b = unbind b in
    let b = Ann (b, ty) in
    let b = unbox (bind_var x (lift b)) in
    let ty0, ctx = infer v_ctx id_ctx (LetIn (t, b)) in
    assert_msg (equal ty ty0)
      (asprintf "check LetIn(ty := %a; ty0 := %a)" 
        Terms.pp ty Terms.pp ty0);
    ctx
  | DCons (id, ts) -> (
    match whnf ty with
    | TCons (_, ts0) ->
      let DConstr (_, pscope) = find_dcons id id_ctx in
      let pscope =
        List.fold_left (fun pscope t ->
          match pscope with
          | PBind (ty, pb) -> subst pb (Ann (t, ty))
          | PBase _ -> pscope) pscope ts0
      in
      let ty0, ctx = infer_pscope v_ctx id_ctx ts pscope in
      assert_msg (equal ty ty0)
        (asprintf "check DCons(@[expected := %a;@;<1 0>actual   := %a@])"
          Terms.pp (nf ty) Terms.pp (nf ty0));
      ctx
    | _ -> 
      assert_msg false
        (asprintf "check DCons(@[t := %a;@;<1 0>ty  := %a@])"
          Terms.pp (nf t) Terms.pp (nf ty)); 
      failwith "")
  | Match (t, mot, pbs) -> (
    match mot with
    | Some _ ->
      let ty0, ctx = 
        infer v_ctx id_ctx (Match (t, mot, pbs))
      in
      assert_msg (equal ty ty0)
        (asprintf "check Match(ty := %a; ty0 := %a)" 
          Terms.pp ty Terms.pp ty0);
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
        | ctx :: ctxs ->
          List.iter (fun ctx0 -> 
            assert_msg (Context.equal ctx ctx0) 
              "check Match2") ctxs;
          (merge ctx1 ctx))
      | _ -> failwith "check Match2")
  | _ ->
    let ty0, ctx = infer v_ctx id_ctx t in
    assert_msg (equal ty ty0) 
      (asprintf "check (@[expected := %a;@;<1 0>actual   := %a@])" 
        Terms.pp (nf ty) Terms.pp (nf ty0));
    ctx

and check_motive cover id_ctx mot m =
  match cover with
  | (v_ctx, t, ty, b, xm) :: cover ->
    let mot0 =
      if m = Ty then subst mot t
      else (
        assert_msg (not (binder_occur mot)) "check_motive";
        snd (unbind mot))
    in
    let mot0 = subst_p mot0 ty in
    let ctx = check v_ctx id_ctx b mot0 in
    let ctx =
      List.fold_left (fun ctx (x, m) -> 
        remove x ctx m) ctx xm
    in
    ctx :: check_motive cover id_ctx mot m
  | _ -> []

and check_cover cover id_ctx ty =
  match cover with
  | (v_ctx, _, _, b, xm) :: cover ->
    let ctx = check v_ctx id_ctx b ty in
    let ctx =
      List.fold_left (fun ctx (x, m) ->
        remove x ctx m) ctx xm
      in
      ctx :: check_cover cover id_ctx ty
  | _ -> []

let rec infer_top v_ctx id_ctx top =
  match top with
  | Empty -> (empty, id_ctx)
  | Define (t, top) ->
    let ty1, ctx1 = infer v_ctx id_ctx t in
    let m, _ = infer_sort v_ctx id_ctx ty1 in
    let ctx2, id_ctx = 
      if m = Ty && is_empty ctx1 
      then infer_top v_ctx id_ctx (subst top t)
      else   
        let x, top = unbind top in
        let ctx2, id_ctx = 
          infer_top (add x (ty1, m) v_ctx) id_ctx top 
        in 
        (remove x ctx2 m, id_ctx)
    in
    (merge ctx1 ctx2, id_ctx)
  | Datype (tcs, top) -> (
    match tcs with
    | TConstr (id, pscope, dcs) ->
      check_pscope v_ctx id_ctx pscope Ty;
      let id_ctx = IdMap.add id (TConstr (id, pscope, [])) id_ctx in
      List.iter (fun (DConstr (_, pscope)) -> 
        check_pscope v_ctx id_ctx pscope Ty;
        param_pscope pscope id []) dcs;
      let id_ctx = IdMap.add id (TConstr (id, pscope, dcs)) id_ctx in
      infer_top v_ctx id_ctx top)

and check_pscope v_ctx id_ctx pscope m =
  match pscope with
  | PBase tscope -> check_tscope v_ctx id_ctx tscope m
  | PBind (t, pscope) ->
    let x, pscope = unbind pscope in
    let m0, _ = infer_sort v_ctx id_ctx t in
    let v_ctx = add x (t, m0) v_ctx in
    check_pscope v_ctx id_ctx pscope (min m m0)

and check_tscope v_ctx id_ctx tscope m =
  match tscope with
  | TBase t ->
    let m0, _ = infer_sort v_ctx id_ctx t in
    assert_msg (m0 <= m) "check_tscope"
  | TBind (t, tscope) ->
    let x, tscope = unbind tscope in
    let m0, _ = infer_sort v_ctx id_ctx t in
    let v_ctx = add x (t, m0) v_ctx in
    check_tscope v_ctx id_ctx tscope (min m m0)

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
        (asprintf "param_tscope(%a; %a)" pp_v x pp_v t);
      param xs ts
    | x :: _, t :: _ -> 
      failwith (asprintf "param_tscope(%a; %a)" pp_v x Terms.pp t);
    | x :: _, [] -> 
      failwith (asprintf "param_tscope(%a; ??)" pp_v x);
  in
  match tscope with
  | TBase ty -> (
    match ty with
    | TCons (id0, ts) ->
      assert_msg (Id.equal id id0) 
        (asprintf "param_tscope(%a)" Terms.pp ty);
      param xs ts
    | _ -> 
      failwith 
        (asprintf "param_tscope(%a)" Terms.pp ty))
  | TBind (_, tscope) ->
      let _, tscope = unbind tscope in
      param_tscope tscope id xs

let tcheck top =
  infer_top empty IdMap.empty top