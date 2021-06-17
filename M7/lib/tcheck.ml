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

let rec infer_sort v_ctx id_ctx ty =
  let sort, v_ctx = infer (pure v_ctx) id_ctx ty in
  match whnf sort with
  | Type   -> (W, v_ctx)
  | Linear -> (One, v_ctx)
  | sort   -> 
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp sort)

and infer v_ctx id_ctx t =
  match t with
  | Var x ->
    let ty, _, m = find x v_ctx in
    (ty, VarMap.add x (ty, One, m) v_ctx)
  | Ann (t, ty) -> (
    match t with
    | LetIn (t, b) ->
      let x, b = unbind b in
      let b = unbox (bind_var x (lift (Ann (b, ty)))) in
      let v_ctx = check v_ctx id_ctx (LetIn (t, b)) ty in
      (ty, v_ctx)
    | _ ->
      let v_ctx = check v_ctx id_ctx t ty in
      (ty, v_ctx))
  | Type -> (Type, v_ctx)
  | Linear -> (Type, v_ctx)
  | TyProd (ty, b) ->
    let x, b = unbind b in
    let sort, v_ctx1 = infer_sort v_ctx id_ctx ty in
    let _, v_ctx2 = 
      infer_sort (VarMap.add x (ty, Zero, sort) v_ctx) id_ctx b 
    in
    let v_ctx2 = VarMap.remove x v_ctx2 in
    (Type, merge v_ctx1 v_ctx2)
  | LnProd (ty, b) ->
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
    let ty1, v_ctx1 = infer v_ctx id_ctx t1 in
    match whnf ty1 with
    | TyProd (ty, b) ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx2 = check v_ctx id_ctx t2 ty in
      (subst b t2, merge v_ctx1 (scale m v_ctx2))
    | LnProd (ty, b) ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx2 = check v_ctx id_ctx t2 ty in
      (subst b t2, merge v_ctx1 (scale m v_ctx2))
    | _ -> failwith (asprintf "infer App(t := %a)" Terms.pp t))
  | LetIn (t, b) ->
    let ty1, v_ctx1 = infer v_ctx id_ctx t in 
    let m, _ = infer_sort v_ctx id_ctx ty1 in
    let ty2, v_ctx2 = 
      if m = W && is_pure v_ctx1 then
        infer v_ctx id_ctx (subst b t)
      else 
        let x, b = unbind b in
        let ty2, v_ctx2 = 
          infer (VarMap.add x (ty1, Zero, m) v_ctx) id_ctx b
        in
        let r = occur x v_ctx2 in
        let v_ctx2 = VarMap.remove x v_ctx2 in
        assert_msg (r <= m)
          (asprintf "infer LetIn(t := %a; m := %a; r := %a)"
            Terms.pp t Rig.pp m Rig.pp r);
        (ty2, v_ctx2)
    in
    (ty2, merge v_ctx1 v_ctx2)
  | TCons (id, ts) ->
    let TConstr (_, tscope, _) = IdMap.find id id_ctx in
    check_constr v_ctx id_ctx ts tscope
  | DCons (id, ts) ->
    let DConstr (_, tscope) = find_dcons id id_ctx in
    check_constr v_ctx id_ctx ts tscope
  | Match (t, opt, pbs) -> (
    let ty, _ = infer v_ctx id_ctx t in
    let m, _ = infer_sort v_ctx id_ctx ty in
    match whnf ty with
    | TCons (id, _) -> (
      let TConstr (_, _, ds) = IdMap.find id id_ctx in
      let cover = coverage v_ctx id_ctx pbs ds in
      match opt with 
      | Some mot -> (
        let ty' = subst_p (subst mot t) ty in
        let v_ctxs = check_cover cover id_ctx mot ty m in
        match v_ctxs with
        | [] -> (ty', v_ctx)
        | (v_ctx) :: v_ctxs -> 
          List.iter 
            (fun v_ctx' ->  
              assert_msg (Context.equal v_ctx v_ctx')  "infer Match0") v_ctxs;
          (ty', v_ctx))
      | _ -> (
        let v_ctxs = infer_cover cover id_ctx in
        match v_ctxs with
        | [] -> failwith "infer Match2"
        | (t, v_ctx) :: v_ctxs -> 
          List.iter 
            (fun (t', v_ctx') ->  
              assert_msg (equal t t')  "infer Match3";
              assert_msg (Context.equal v_ctx v_ctx')  
                (asprintf "infer Match4(%a; %a)"
                  Context.pp v_ctx Context.pp v_ctx')) v_ctxs;
          (t, v_ctx)))
    | _ -> failwith "infer Match5")
  | Axiom (_, ty) ->
    let _ = infer_sort v_ctx id_ctx ty in
    (ty, v_ctx)

and coverage v_ctx id_ctx pbs ds =
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
  let rec arity v_ctx tscope xs =
    match tscope, xs with
    | Bind (ty, tscope), x :: xs ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx = VarMap.add x (ty, Zero, m) v_ctx in
      let tscope = subst tscope (Var x) in
      let (v_ctx, ty, xm) = arity v_ctx tscope xs in
      (v_ctx, ty, (x, m) :: xm)
    | Base ty, [] -> (v_ctx, ty, [])
    | _ -> failwith "arity"
  in
  match pbs with
  | pb :: pbs -> (
    let p, b = unbind_p pb in
    match p with
    | PDCons (id, ps) ->
      let xs = List.map strip ps in 
      let (DConstr (_, tscope), ds) = find id ds in
      let (v_ctx', ty, xm) = arity v_ctx tscope xs in
      let ds = coverage v_ctx id_ctx pbs ds in 
      (v_ctx', ty, b, xm) :: ds
    | _ -> failwith "coverage")
  | [] -> (
    match ds with
    | [] -> []
    | _ -> failwith "coverage")

and check v_ctx id_ctx t ty =
  let m, _ = infer_sort v_ctx id_ctx ty in
  match t with
  | Lambda b -> (
    let x, b1 = unbind b in
    match whnf ty with
    | TyProd (ty, b2) ->
      let b2 = subst b2 (Var x) in
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx1 =
        check (VarMap.add x (ty, Zero, m) (pure v_ctx)) id_ctx b1 b2
      in
      let r = occur x v_ctx1 in
      let v_ctx' = VarMap.remove x v_ctx1 in
      assert_msg (r <= m)
        (asprintf "check Lambda(m := %a, r := %a)"
          Rig.pp m Rig.pp r);
      v_ctx'
    | LnProd (ty, b2) ->
      let b2 = subst b2 (Var x) in
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx' = 
        check (VarMap.add x (ty, Zero, m) v_ctx) id_ctx b1 b2 
      in
      let r = occur x v_ctx' in
      let v_ctx' = VarMap.remove x v_ctx' in
      assert_msg (r <= m)
        (asprintf "check Lambda(m := %a, r := %a)"
          Rig.pp m Rig.pp r);
      v_ctx'
    | _ -> 
      failwith
        (asprintf "@[check Lambda(@;<1 2>t := %a;@;<1 2>ty := %a)@]" 
          Terms.pp t Terms.pp ty))
  | Fix b ->
    let x, b = unbind b in
    let v_ctx' = 
      check (pure (VarMap.add x (ty, Zero, m) v_ctx)) id_ctx b ty
    in
    VarMap.remove x v_ctx'
  | LetIn (t, b) ->
    let x, b = unbind b in
    let b = Ann (b, ty) in
    let b = unbox (bind_var x (lift b)) in
    let ty', v_ctx' = infer v_ctx id_ctx (LetIn (t, b)) in
    assert_msg (equal ty ty')
      (asprintf "check LetIn(ty := %a; ty' := %a)" 
        Terms.pp ty Terms.pp ty');
    v_ctx'
  | Match (t, opt, pbs) -> (
    match opt with
    | Some _ ->
      let ty', v_ctx' = 
        infer v_ctx id_ctx (Match (t, opt, pbs)) 
      in
      assert_msg (equal ty ty')
        (asprintf "check Match(ty := %a; ty' := %a)" 
          Terms.pp ty Terms.pp ty');
      v_ctx'
    | _ ->
      let ty, _ = infer v_ctx id_ctx t in
      let _ = infer_sort v_ctx id_ctx ty in
      match whnf ty with
      | TCons (id, _) -> (
        let TConstr (_, _, ds) = IdMap.find id id_ctx in
        let cover = coverage v_ctx id_ctx pbs ds in
        let v_ctxs = infer_cover cover id_ctx in
        match v_ctxs with
        | [] -> failwith "check Match0"
        | (t, v_ctx) :: v_ctxs -> 
          List.iter 
            (fun (t', v_ctx') ->  
              assert_msg (equal t t')  "check Match1";
              assert_msg (Context.equal v_ctx v_ctx')  
                (asprintf "check Match2(%a; %a)" 
                  Context.pp v_ctx Context.pp v_ctx')) v_ctxs;
          (v_ctx))
      | _ -> failwith "check Match3")
  | _ ->
    let ty', v_ctx' = infer v_ctx id_ctx t in
    assert_msg (equal ty ty')
      (asprintf "check (ty := %a; ty' := %a)" 
        Terms.pp ty Terms.pp ty');
    v_ctx'

and check_cover cover id_ctx mot ty m =
  match cover with
  | (v_ctx, t, b, xm) :: cover ->
    let x, mot' = unbind mot in
    let v_ctx = VarMap.add x (ty, Zero, m) v_ctx in
    let mot' = subst_p mot' t in
    let v_ctx = check v_ctx id_ctx b mot' in
    let v_ctx = 
      List.fold_left
        (fun v_ctx (x, m) -> 
          let r = occur x v_ctx in
          assert_msg (r <= m) 
            (asprintf "infer_cover(r := %a; m := %a)" Rig.pp r Rig.pp m);
          VarMap.remove x v_ctx)
        v_ctx ((x, m) :: xm)
    in
    v_ctx :: check_cover cover id_ctx mot ty m
  | _ -> []

and infer_cover cover id_ctx =
  match cover with
  | (v_ctx, _, b, xm) :: cover ->
    let ty, v_ctx = infer v_ctx id_ctx b in
    let v_ctx = 
      List.fold_left 
        (fun v_ctx (x, m) -> 
          let r = occur x v_ctx in 
          assert_msg (r <= m) 
            (asprintf "infer_cover(r := %a; m := %a)" Rig.pp r Rig.pp m);
          VarMap.remove x v_ctx)
        v_ctx xm
    in 
    (ty, v_ctx) :: infer_cover cover id_ctx
  | _ -> []


and check_constr v_ctx id_ctx ts tscope =
  match ts, tscope with
  | t :: ts, Bind (ty, tscope) ->
    let v_ctx1 = check v_ctx id_ctx t ty in
    let ty, v_ctx2 = check_constr v_ctx id_ctx ts (subst tscope t) in
    (ty, merge v_ctx1 v_ctx2)
  | [], Base ty -> (ty, v_ctx)
  | _ -> failwith "check_scope"

and t_of_p = function
  | PVar x -> Var x
  | PTCons (id, ps) ->
    TCons (id, List.map t_of_p ps)
  | PDCons (id, ps) ->
    DCons (id, List.map t_of_p ps)

let rec infer_top v_ctx id_ctx top =
  match top with
  | Empty -> (v_ctx, id_ctx)
  | Define (t, top) ->
    let ty1, v_ctx1 = infer v_ctx id_ctx t in 
    let m, _ = infer_sort v_ctx id_ctx ty1 in
    let v_ctx2, id_ctx2 = 
      if m = W && is_pure v_ctx1 then
        let x, _ = unbind top in
        let v_ctx = VarMap.add x (ty1, Zero, m) v_ctx in
        infer_top v_ctx id_ctx (subst top t)
      else 
        let x, top = unbind top in
        let v_ctx2, id_ctx2 = 
          infer_top (VarMap.add x (ty1, Zero, m) v_ctx) id_ctx top
        in
        let r = occur x v_ctx2 in
        assert_msg (r <= m)
          (asprintf "infer LetIn(t := %a; m := %a; r := %a)"
            Terms.pp t Rig.pp m Rig.pp r);
        (v_ctx2, id_ctx2)
    in
    (merge v_ctx1 v_ctx2, id_ctx2)
  | Datype (tcs, top) -> (
    match tcs with
    | TConstr (id, tscope, dcs) -> 
      let _ = check_tscope v_ctx id_ctx tscope in 
      let id_ctx = IdMap.add id (TConstr (id, tscope, [])) id_ctx in
      let _ =
        List.map 
          (fun (DConstr (_, tscope)) ->
            check_tscope v_ctx id_ctx tscope) dcs
      in 
      let id_ctx = IdMap.add id (TConstr (id, tscope, dcs)) id_ctx in
      infer_top v_ctx id_ctx top)

and check_tscope v_ctx id_ctx tscope =
  match tscope with
  | Base t -> infer_sort v_ctx id_ctx t
  | Bind (t, tscope) ->
    let x, tscope = unbind tscope in
    let m, _ = infer_sort v_ctx id_ctx t in
    let v_ctx = VarMap.add x (t, Zero, m) v_ctx in
    check_tscope v_ctx id_ctx tscope