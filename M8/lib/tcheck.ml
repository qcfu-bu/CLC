open Bindlib
open Format
open Rig
open Names
open Terms
open Context
open Equality

let assert_msg cond msg = 
  if cond then ()
  else (prerr_endline msg; assert false)

let rig_of_sort ty =
  match whnf ty with
  | Type -> W
  | Linear -> One
  | _ -> failwith "sort expected"

let sort_of_rig = function
  | W -> Type
  | One -> Linear
  | Zero -> failwith "non-Zero rig expected"

let rec t_of_p = function
  | PVar x -> Var x
  | PTCons (id, ps) ->
    TCons (id, List.map t_of_p ps)
  | PDCons (id, ps) ->
    DCons (id, List.map t_of_p ps)

let rec coverage v_ctx id_ctx pbs ds ts =
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
      let (v_ctx, ty, xm) = arity_pscope v_ctx pscope ts xs in
      (v_ctx, ty, xm)
    | PBase tscope, _ -> arity_tscope v_ctx tscope xs
    | _ -> failwith "arity_pscope"
  and arity_tscope v_ctx tscope xs =
    match tscope, xs with
    | TBind (ty, (r, tscope)), x :: xs ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx = VarMap.add x (ty, Zero, m) v_ctx in
      let tscope = subst tscope (Var x) in
      let (v_ctx, ty, xm) = arity_tscope v_ctx tscope xs in
      (v_ctx, ty, (x, m * r) :: xm)
    | TBase ty, [] -> (v_ctx, ty, [])
    | _ -> failwith "arity_tscope"
  in
  match pbs with
  | pb :: pbs -> (
    let p, b = unbind_p pb in
    match p with
    | PDCons (id, ps) ->
      let xs = List.map strip ps in 
      let t = t_of_p p in
      let (DConstr (_, pscope), ds) = find id ds in
      let (v_ctx', ty, xm) = arity_pscope v_ctx pscope ts xs in
      let ds = coverage v_ctx id_ctx pbs ds ts in 
      (v_ctx', t, ty, b, xm) :: ds
    | _ -> failwith "coverage")
  | [] -> (
    match ds with
    | [] -> []
    | _ -> failwith "coverage")

and infer_sort v_ctx id_ctx ty =
  let sort, v_ctx = infer v_ctx id_ctx ty Zero in
  match whnf sort with
  | Type -> (W, v_ctx)
  | Linear -> (One, v_ctx)
  | sort ->
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp sort)

and infer v_ctx id_ctx t q =
  match t with
  | Var x ->
    let ty, _, m = find x v_ctx in
    (ty, VarMap.add x (ty, q, m) v_ctx)
  | Ann (t, ty) -> (
    match t with
    | LetIn (t, r, b) ->
      let x, b = unbind b in
      let b = unbox (bind_var x (lift (Ann (b, ty)))) in
      let v_ctx = check v_ctx id_ctx (LetIn (t, r, b)) ty q in
      (ty, v_ctx)
    | _ ->
      let v_ctx = check v_ctx id_ctx t ty q in
      (ty, v_ctx))
  | Type -> (Type, v_ctx)
  | Linear -> (Type, v_ctx)
  | TyProd (ty, _, b) ->
    let x, b = unbind b in
    let sort, v_ctx1 = infer_sort v_ctx id_ctx ty in
    let _, v_ctx2 =
      infer_sort (VarMap.add x (ty, Zero, sort) v_ctx) id_ctx b
    in 
    let v_ctx2 = VarMap.remove x v_ctx2 in
    (Type, merge v_ctx1 v_ctx2)
  | LnProd (ty, _, b) ->
    let x, b = unbind b in
    let sort, v_ctx1 = infer_sort v_ctx id_ctx ty in
    let _, v_ctx2 =
      infer_sort (VarMap.add x (ty, Zero, sort) v_ctx) id_ctx b
    in
    let v_ctx2 = VarMap.remove x v_ctx2 in
    (Linear, merge v_ctx1 v_ctx2)
  | Lambda _ -> failwith (asprintf "infer Lambda(%a)" Terms.pp t)
  | Fix _ -> failwith (asprintf "infer Fix(%a)" Terms.pp t)
  | App (t1, t2) -> (
    let ty1, v_ctx1 = infer v_ctx id_ctx t1 q in
    match whnf ty1 with
    | TyProd (ty, r, b) ->
      let q' = if q = Zero || r = Zero then Zero else One in
      let _ = infer_sort v_ctx id_ctx ty in
      let v_ctx2 = check v_ctx id_ctx t2 ty q' in
      (subst b t2, merge v_ctx1 v_ctx2)
    | LnProd (ty, r, b) ->
      let q' = if q = Zero || r = Zero then Zero else One in
      let _ = infer_sort v_ctx id_ctx ty in
      let v_ctx2 = check v_ctx id_ctx t2 ty q' in
      (subst b t2, merge v_ctx1 v_ctx2)
    | _ -> failwith (asprintf "@[infer App(t :=@;<1 2>%a)@]" Terms.pp t))
  | LetIn (t, r, b) ->
    let q' = if q = Zero || r = Zero then Zero else One in
    let ty1, v_ctx1 = infer v_ctx id_ctx t q' in
    let m, _ = infer_sort v_ctx id_ctx ty1 in
    let ty2, v_ctx2 =
      if is_pure v_ctx1 then
        infer v_ctx id_ctx (subst b t) q
      else
        let x, b = unbind b in
        let ty2, v_ctx2 = 
          infer (VarMap.add x (ty1, Zero, m) v_ctx) id_ctx b q
        in
        let r' = occur x v_ctx2 in
        let v_ctx2 = VarMap.remove x v_ctx2 in
        assert_msg (r' <= m * r)
          (asprintf "infer LetIn(t := %a; m := %a; r := %a)"
            Terms.pp t Rig.pp m Rig.pp r);
        (ty2, v_ctx2)
    in
    (ty2, merge v_ctx1 v_ctx2)
  | TCons (id, ts) ->
    let TConstr (_, pscope, _) = IdMap.find id id_ctx in
    infer_pscope v_ctx id_ctx ts pscope Zero
  | DCons (id, ts) -> (
    match find_dcons id id_ctx with
    | DConstr (_, PBase tscope) ->
      infer_tscope v_ctx id_ctx ts tscope q
    | _ -> failwith (asprintf "infer DCons(%a)" Terms.pp t))
  | Match (t, opt, pbs) -> (
    let ty, v_ctx1 = infer v_ctx id_ctx t q in
    let ty = whnf ty in
    match ty with
    | TCons (id, ts) -> (
      let TConstr (_, _, ds) = IdMap.find id id_ctx in
      let cover = coverage v_ctx id_ctx pbs ds ts in
      match opt with
      | Some mot -> (
        let ty' = subst_p (subst mot t) ty in
        let v_ctxs = check_motive cover id_ctx mot q in
        match v_ctxs with
        | [] -> (ty', v_ctx)
        | v_ctx2 :: v_ctxs ->
          List.iter
            (fun v_ctx ->
              assert_msg (Context.equal v_ctx2 v_ctx) "infer Match0") v_ctxs;
          (ty', merge v_ctx1 v_ctx2))
      | _ -> (
        let v_ctxs = infer_cover cover id_ctx q in
        match v_ctxs with
        | [] -> failwith "infer Match2"
        | (t, v_ctx2) :: v_ctxs ->
          List.iter
            (fun (t', v_ctx) ->
              assert_msg (equal t t')  
                (asprintf "infer Match3(%a;@;<1 2>%a)"
                  Terms.pp t Terms.pp t');
              assert_msg (Context.equal v_ctx2 v_ctx)  
                (asprintf "infer Match4(%a;@;<1 2>%a)"
                  Context.pp v_ctx Context.pp v_ctx)) v_ctxs;
            (t, merge v_ctx1 v_ctx2)))
    | _ -> failwith "infer Match5")
  | Axiom (_, ty) ->
    let _ = infer_sort v_ctx id_ctx ty in
    (ty, v_ctx)

and infer_pscope v_ctx id_ctx ts pscope q =
  match ts, pscope with
  | t :: ts, PBind (ty, pscope) ->
    let v_ctx1 = check v_ctx id_ctx t ty Zero in
    let ty, v_ctx2 = 
      infer_pscope v_ctx id_ctx ts (subst pscope (Ann (t, ty))) q
    in
    (ty, merge v_ctx1 v_ctx2)
  | ts, PBase pscope -> infer_tscope v_ctx id_ctx ts pscope q
  | _ -> 
    failwith 
      (asprintf "infer_pscope(%a; %d)" 
        pp_pscope pscope (List.length ts))

and infer_tscope v_ctx id_ctx ts tscope q =
  match ts, tscope with
  | t :: ts, TBind (ty, (r, tscope)) ->
    let q' = if q = Zero || r = Zero then Zero else One in
    let v_ctx1 = check v_ctx id_ctx t ty q' in
    let ty, v_ctx2 = 
      infer_tscope v_ctx id_ctx ts (subst tscope (Ann (t, ty))) q
    in
    (ty, merge v_ctx1 v_ctx2)
  | [], TBase ty -> (ty, v_ctx)
  | _ -> failwith "infer_tscope"

and infer_cover cover id_ctx q =
  match cover with
  | (v_ctx, _, _, b, xm) :: cover ->
    let ty, v_ctx = infer v_ctx id_ctx b q in
    let v_ctx =
      List.fold_left
        (fun v_ctx (x, m) -> 
          let r = occur x v_ctx in 
          assert_msg (r <= m) 
            (asprintf "infer_cover(r := %a; m := %a)" Rig.pp r Rig.pp m);
          VarMap.remove x v_ctx)
        v_ctx xm
    in 
    (ty, v_ctx) :: infer_cover cover id_ctx q
  | _ -> []

and check v_ctx id_ctx t ty q =
  let m, _ = infer_sort v_ctx id_ctx ty in
  match t with
  | Lambda b1 -> (
    let x, b1 = unbind b1 in
    match whnf ty with
    | TyProd (ty, r, b2) ->
      let b2 = subst b2 (Var x) in
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx1 =
        check (VarMap.add x (ty, Zero, m) v_ctx) id_ctx b1 b2 q
      in
      let r' = occur x v_ctx1 in
      let v_ctx1 = VarMap.remove x v_ctx1 in
      assert_msg (r' <= m * r && is_pure v_ctx1)
        (asprintf "check Lambda(x := %s, r' := %a, m * r := %a)"
          (name_of x) Rig.pp r' Rig.pp (m * r));
      v_ctx1
    | LnProd (ty, r, b2) ->
      let b2 = subst b2 (Var x) in
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx1 =
        check (VarMap.add x (ty, Zero, m) v_ctx) id_ctx b1 b2 q
      in
      let r' = occur x v_ctx1 in
      let v_ctx1 = VarMap.remove x v_ctx1 in
      assert_msg (r' <= m * r)
        (asprintf "check Lambda(x := %s, m := %a, r := %a)"
          (name_of x) Rig.pp m Rig.pp r);
      v_ctx1
    | _ -> 
      failwith
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@]" 
          Terms.pp t Terms.pp ty))
  | Fix b ->
    let x, b = unbind b in
    let v_ctx = 
      check (VarMap.add x (ty, Zero, m) v_ctx) id_ctx b ty q
    in
    assert_msg (is_pure v_ctx)
      (asprintf "check Fix(x := %s)" (name_of x));
    VarMap.remove x v_ctx
  | LetIn (t, r, b) ->
    let x, b = unbind b in
    let b = Ann (b, ty) in
    let b = unbox (bind_var x (lift b)) in
    let ty', v_ctx' = infer v_ctx id_ctx (LetIn (t, r, b)) q in
    assert_msg (equal ty ty')
      (asprintf "check LetIn(ty := %a; ty' := %a)" 
        Terms.pp ty Terms.pp ty');
    v_ctx'
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
      let ty', v_ctx = infer_pscope v_ctx id_ctx ts pscope q in
      assert_msg (equal ty ty') 
        (asprintf "check DCons(@[expected := %a;@;<1 0>actual   := %a@])"
          Terms.pp (whnf ty) Terms.pp (whnf ty'));
      v_ctx
    | _ -> 
      assert_msg false
        (asprintf "check DCons(@[t := %a;@;<1 0>ty  := %a@])"
          Terms.pp (whnf t) Terms.pp (whnf ty)); 
      failwith "")
  | Match (t, opt, pbs) -> (
    match opt with
    | Some _ ->
      let ty', v_ctx' = 
        infer v_ctx id_ctx (Match (t, opt, pbs)) q
      in
      assert_msg (equal ty ty')
        (asprintf "check Match(ty := %a; ty' := %a)" 
          Terms.pp ty Terms.pp ty');
      v_ctx'
    | _ ->
      let ty1, v_ctx1 = infer v_ctx id_ctx t q in
      let _ = infer_sort v_ctx id_ctx ty1 in
      let ty1 = whnf ty1 in
      match ty1 with
      | TCons (id, ts) -> (
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover = coverage v_ctx id_ctx pbs ds ts in
        let v_ctxs = check_cover cover id_ctx ty q in
        match v_ctxs with
        | [] -> v_ctx1
        | v_ctx2 :: v_ctxs -> 
          List.iter 
            (fun v_ctx ->  
              assert_msg (Context.equal v_ctx2 v_ctx)  
                (asprintf "check Match1(%a; %a)" 
                  Context.pp v_ctx2 Context.pp v_ctx)) v_ctxs;
          (merge v_ctx1 v_ctx2))
      | _ -> failwith "check Match2")
  | _ ->
    let ty', v_ctx' = infer v_ctx id_ctx t q in
    assert_msg (equal ty ty')
      (asprintf "check (@[expected := %a;@;<1 0>actual   := %a@])" 
        Terms.pp (nf ty) Terms.pp (nf ty'));
    v_ctx'

and check_motive cover id_ctx mot q =
  match cover with
  | (v_ctx, t, ty, b, xm) :: cover ->
    let mot' = subst_p (subst mot t) ty in
    let v_ctx = check v_ctx id_ctx b mot' q in
    let v_ctx =
      List.fold_left
        (fun v_ctx (x, m) -> 
          let r = occur x v_ctx in
          assert_msg (r <= m) 
            (asprintf "check_motive(x := %a; r := %a; m := %a)" 
              pp_v x Rig.pp r Rig.pp m);
          VarMap.remove x v_ctx)
      v_ctx xm
    in
    v_ctx :: check_motive cover id_ctx mot q
  | _ -> []

and check_cover cover id_ctx ty q =
  match cover with
  | (v_ctx, _, _, b, xm) :: cover ->
    let v_ctx = check v_ctx id_ctx b ty q in
    let v_ctx = 
      List.fold_left 
        (fun v_ctx (x, m) -> 
          let r = occur x v_ctx in 
          assert_msg (r <= m) 
            (asprintf "infer_cover(x := %a; r := %a; m := %a)" 
              pp_v x Rig.pp r Rig.pp m);
          VarMap.remove x v_ctx)
        v_ctx xm
    in 
    v_ctx :: check_cover cover id_ctx ty q
  | _ -> []

let rec infer_top v_ctx id_ctx top =
  match top with
  | Empty -> (v_ctx, id_ctx)
  | Define (t, r, top) ->
    let ty1, v_ctx1 = infer v_ctx id_ctx t r in 
    let m, _ = infer_sort v_ctx id_ctx ty1 in
    let v_ctx2, id_ctx2 = 
      if is_pure v_ctx1 then
        let x, _ = unbind top in
        let v_ctx = VarMap.add x (ty1, Zero, m) v_ctx in
        infer_top v_ctx id_ctx (subst top t)
      else 
        let x, top = unbind top in
        let v_ctx2, id_ctx2 = 
          infer_top (VarMap.add x (ty1, Zero, m) v_ctx) id_ctx top
        in
        let r' = occur x v_ctx2 in
        assert_msg (r' <= m * r)
          (asprintf "infer LetIn(t := %a; m := %a; r := %a)"
            Terms.pp t Rig.pp m Rig.pp r);
        (v_ctx2, id_ctx2)
    in
    (merge v_ctx1 v_ctx2, id_ctx2)
  | Datype (tcs, top) -> (
    match tcs with
    | TConstr (id, pscope, dcs) -> 
      check_pscope v_ctx id_ctx pscope;
      let id_ctx = IdMap.add id (TConstr (id, pscope, [])) id_ctx in
      List.iter
        (fun (DConstr (_, pscope)) ->
          check_pscope v_ctx id_ctx pscope;
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
    | TCons (id', ts) ->
      assert_msg (Id.equal id id') 
        (asprintf "param_tscope(%a)" Terms.pp ty);
      param xs ts
    | _ -> 
      failwith 
        (asprintf "param_tscope(%a)" Terms.pp ty))
  | TBind (_, (_, tscope)) ->
    let _, tscope = unbind tscope in
    param_tscope tscope id xs

and check_pscope v_ctx id_ctx pscope =
  match pscope with
  | PBase tscope -> check_tscope v_ctx id_ctx tscope false
  | PBind (t, pscope) ->
    let x, pscope = unbind pscope in
    let m', _ = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, Zero, m') v_ctx in
    check_pscope v_ctx id_ctx pscope

and check_tscope v_ctx id_ctx tscope q =
  match tscope with
  | TBase t -> 
    let m, _ = infer_sort v_ctx id_ctx t in
    assert_msg (not (q && m != One))
      (asprintf "check_tscope(m := %a; q := %b)" Rig.pp m q)
  | TBind (t, (r, tscope)) ->
    let x, tscope = unbind tscope in
    let m, _ = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, Zero, m) v_ctx in
    check_tscope v_ctx id_ctx tscope (q || (m * r = One))

let infer top =
  infer_top VarMap.empty IdMap.empty top