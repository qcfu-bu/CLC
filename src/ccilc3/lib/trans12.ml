open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

type ctx =
  { vs : tm VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let msubst_ctx map ctx =
  let vs = VMap.map (fun a -> msubst map a) ctx.vs in
  { ctx with vs }

let subst_ctx x ctx m =
  let ctx = { ctx with vs = VMap.remove x ctx.vs } in
  msubst_ctx (VMap.singleton x m) ctx

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

let assert_equal env eqns map m n =
  if equal rd_all env m n then
    (eqns, map)
  else
    (Meta.Eq (env, m, n) :: eqns, map)

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

let rec infer_sort ctx env eqns map m =
  let a, eqns, map = infer_tm ctx env eqns map m in
  let a = Meta.resolve_tm map a in
  match whnf rd_all env a with
  | Type s -> (s, eqns, map)
  | _ -> failwith "infer_sort(%a)" pp_tm a

and infer_tm ctx env eqns map m =
  match m with
  | Ann (a, m) -> (
    let _, eqns, map = infer_sort ctx env eqns map a in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let eqns, map = check_tm ctx env eqns map (Let (m, abs)) a in
      (a, eqns, map)
    | _ ->
      let eqns, map = check_tm ctx env eqns map m a in
      (a, eqns, map))
  | Meta (x, xs) -> (
    match MMap.find_opt x map with
    | Some (_, Some a) -> (a, eqns, map)
    | _ ->
      let meta, _ = meta_mk ctx in
      (meta, eqns, MMap.add x (None, Some meta) map))
  | Type _ -> (Type U, eqns, map)
  | Var x -> (
    match VMap.find_opt x ctx.vs with
    | Some a -> (a, eqns, map)
    | _ -> failwith "infer_tm(%a)" V.pp x)
  | Pi (s, a, impl, abs) ->
    let x, b = unbind_tm abs in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let ctx = { ctx with vs = VMap.add x a ctx.vs } in
    let _, eqns, map = infer_sort ctx env eqns map b in
    (Type s, eqns, map)
  | Fun (a_opt, cls) -> (
    match a_opt with
    | Some a ->
      let _, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map (Fun (a_opt, cls)) a in
      (a, eqns, map)
    | None -> failwith "infer_tm(%a)" pp_tm m)
  | App (m, n) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Pi (_, a, impl, abs) ->
      if impl then
        let x, b = unbind_tm abs in
        let meta, meta_x = meta_mk ctx in
        let b = subst x b meta in
        let z = V.mk "" in
        let map = MMap.add meta_x (None, Some a) map in
        let ctx = { ctx with vs = VMap.add z b ctx.vs } in
        infer_tm ctx env eqns map (App (Var z, n))
      else
        let x, b = unbind_tm abs in
        let eqns, map = check_tm ctx env eqns map n a in
        (subst x b (Ann (a, n)), eqns, map)
    | a -> (fst (meta_mk ctx), eqns, map))
  | Let (m, abs) ->
    let a, eqns, map = infer_tm ctx env eqns map m in
    let s, eqns, map = infer_sort ctx env eqns map a in
    let m = Meta.resolve_tm map m in
    let a = Meta.resolve_tm map a in
    let x, n = unbind_tm abs in
    let ctx = { ctx with vs = VMap.add x a ctx.vs } in
    let env =
      match s with
      | U -> VMap.add x m env
      | L -> env
    in
    infer_tm ctx env eqns map n
  | Data (d, ms) -> (
    let ptl, _ = DMap.find d ctx.ds in
    try infer_ptl ctx env eqns map ms ptl with
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Cons (c, ms) -> (
    let ptl = CMap.find c ctx.cs in
    try infer_ptl ctx env eqns map ms ptl with
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Absurd -> failwith "infer_tm(%a)" pp_tm m
  | Match (ms, cls) ->
    let ms_ty, eqns, map =
      List.fold_left
        (fun (acc, eqns, map) m ->
          let a, eqns, map = infer_tm ctx env eqns map m in
          (a :: acc, eqns, map))
        ([], eqns, map) ms
    in
    let meta, meta_x = meta_mk ctx in
    let a =
      List.fold_left
        (fun acc m_ty ->
          let x = V.mk "" in
          Pi (L, m_ty, false, bind_tm x acc))
        meta ms_ty
    in
    let prbm = Var.prbm_of_cls cls in
    let eqns, map = check_prbm ctx env eqns map prbm a in
    let map = Meta.unify map eqns in
    (Meta.resolve_tm map meta, eqns, map)
  | If (m, tt, ff) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Data (d, _) ->
      let _, cs = DMap.find d ctx.ds in
      if List.length cs = 2 then
        let tt_ty, eqns, map = infer_tm ctx env eqns map tt in
        let ff_ty, eqns, map = infer_tm ctx env eqns map ff in
        let eqns, map = assert_equal env eqns map tt_ty ff_ty in
        (tt_ty, eqns, map)
      else
        failwith "infer_tm(%a)" pp_tm m
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Main -> (Type L, eqns, map)
  | Proto -> (Type U, eqns, map)
  | End -> (Proto, eqns, map)
  | Act (r, a, abs) ->
    let s, eqns, map = infer_sort ctx env eqns map a in
    let x, b = unbind_tm abs in
    let ctx = { ctx with vs = VMap.add x a ctx.vs } in
    let eqns, map = check_tm ctx env eqns map b Proto in
    (Proto, eqns, map)
  | Ch (r, m) ->
    let eqns, map = check_tm ctx env eqns map m Proto in
    (Type L, eqns, map)
  | Fork (a, m, abs) -> (
    let _, eqns, map = infer_sort ctx env eqns map a in
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (r, a) ->
      let x, n = unbind_tm abs in
      let eqns, map = check_tm ctx env eqns map a Proto in
      let eqns, map = check_tm ctx env eqns map m Main in
      let unit = Data (Prelude.unit_d, []) in
      let ctx = { ctx with vs = VMap.add x (Ch (r, a)) ctx.vs } in
      let eqns, map = check_tm ctx env eqns map n unit in
      let a = Ch (not r, a) in
      (Data (Prelude.tnsr_d, [ a; Main ]), eqns, map)
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Send m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 = true ->
      let x, b = unbind_tm abs in
      let abs = bind_tm x (Ch (r1, b)) in
      (Pi (L, a, false, abs), eqns, map)
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Recv m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 = false -> (
      let x, b = unbind_tm abs in
      let s, eqns, map = infer_sort ctx env eqns map a in
      match s with
      | U ->
        let cls = Cl (bindp_tm_opt [ PVar x ] (Some (Ch (r1, b)))) in
        let abs = bind_cls V.blank [ cls ] in
        (Data (Prelude.sig_d, [ a; Fun (None, abs) ]), eqns, map)
      | L -> (Data (Prelude.tnsr_d, [ a; Ch (r1, b) ]), eqns, map))
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Close m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (_, End) -> (Data (Prelude.unit_d, []), eqns, map)
    | _ -> failwith "infer_tm(%a)" pp_tm m)

and infer_ptl ctx env eqns map ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, impl, abs) ->
    if impl then
      let meta, meta_x = meta_mk ctx in
      let map = MMap.add meta_x (None, Some a) map in
      let x, ptl = unbind_ptl abs in
      infer_ptl ctx env eqns map (m :: ms) (subst_ptl x ptl meta)
    else
      let s, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map m a in
      let x, ptl = unbind_ptl abs in
      infer_ptl ctx env eqns map ms (subst_ptl x ptl (Ann (a, m)))
  | ms, PBase tl -> infer_tl ctx env eqns map ms tl
  | _ -> failwith "infer_ptl"

and infer_tl ctx env eqns map ms tl =
  match (ms, tl) with
  | m :: ms, TBind (a, impl, abs) ->
    if impl then
      let meta, meta_x = meta_mk ctx in
      let map = MMap.add meta_x (None, Some a) map in
      let x, tl = unbind_tl abs in
      infer_tl ctx env eqns map (m :: ms) (subst_tl x tl meta)
    else
      let s, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map m a in
      let x, ptl = unbind_tl abs in
      infer_tl ctx env eqns map ms (subst_tl x tl (Ann (a, m)))
  | [], TBase a ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    (a, eqns, map)
  | _ -> failwith "infer_tl"

and check_tm ctx env eqns map m a =
  match m with
  | Meta (x, _) -> (eqns, MMap.add x (None, Some a) map)
  | Fun (b_opt, abs) ->
    let eqns, map =
      match b_opt with
      | Some b -> assert_equal env eqns map a b
      | None -> (eqns, map)
    in
    let x, cls = unbind_cls abs in
    let ctx = { ctx with vs = VMap.add x a ctx.vs } in
    let prbm = Var.prbm_of_cls cls in
    check_prbm ctx env eqns map prbm a
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, eqns, map = infer_tm ctx env eqns map (Let (m, abs)) in
    assert_equal env eqns map a b
  | Cons (c, ms) -> (
    let a = Meta.resolve_tm map a in
    match whnf rd_all env a with
    | Data (_, ns) ->
      let ptl = CMap.find c ctx.cs in
      let ptl =
        List.fold_left
          (fun ptl n ->
            match ptl with
            | PBind (a, _, abs) ->
              let x, ptl = unbind_ptl abs in
              subst_ptl x ptl (Ann (a, n))
            | PBase _ -> ptl)
          ptl ns
      in
      let b, eqns, map = infer_ptl ctx env eqns map ms ptl in
      assert_equal env eqns map a b
    | _ ->
      let b, eqns, map = infer_tm ctx env eqns map m in
      assert_equal env eqns map a b)
  | Match (ms, cls) ->
    let ms_ty, eqns, map =
      List.fold_left
        (fun (acc, eqns, map) m ->
          let a, eqns, map = infer_tm ctx env eqns map m in
          (a :: acc, eqns, map))
        ([], eqns, map) ms
    in
    let a =
      List.fold_left
        (fun acc m_ty ->
          let x = V.mk "" in
          Pi (L, m_ty, false, bind_tm x acc))
        a ms_ty
    in
    let prbm = Var.prbm_of_cls cls in
    let eqns, map = check_prbm ctx env eqns map prbm a in
    (eqns, map)
  | _ ->
    let b, eqns, map = infer_tm ctx env eqns map m in
    assert_equal env eqns map a b

and check_prbm ctx env eqns map prbm a =
  let rec absurd_split es rhs =
    match (es, rhs) with
    | Var.Eq (_, Var _, Absurd, _) :: _, None -> true
    | Var.Eq (_, Var _, Absurd, _) :: _, Some _ -> failwith "absurd_split"
    | _ :: es, _ -> absurd_split es rhs
    | [], _ -> false
  in
  let rec can_split es =
    match es with
    | Var.Eq (_, Var _, Cons (_, _), _) :: _ -> true
    | _ :: es -> can_split es
    | [] -> false
  in
  let rec first_split es =
    match es with
    | Var.Eq (_, Var x, Cons (c, ms), a) :: _ -> (x, c, ms, a)
    | _ :: es -> first_split es
    | [] -> failwith "first_split"
  in
  match prbm.clause with
  | [] -> (
    if has_failed (fun () -> Var.unify prbm.global) then
      (eqns, map)
    else
      let a = whnf rd_all env a in
      match a with
      | Pi (_, a, _, _) -> (
        let a = whnf rd_all env a in
        match a with
        | Data (d, _) ->
          let _, cs = DMap.find d ctx.ds in
          if cs <> [] then
            failwith "check_prbm"
          else
            (eqns, map)
        | _ -> failwith "check_prbm")
      | _ -> failwith "check_prbm")
  | (es, ps, rhs) :: _ when absurd_split es rhs ->
    if has_failed (fun () -> Var.unify prbm.global) then
      (eqns, map)
    else
      failwith "check_prbm"
  | (es, ps, rhs) :: _ when can_split es -> (
    let x, c, _, b = first_split es in
    let s, eqns, map = infer_sort ctx env eqns map b in
    let b = whnf rd_all env b in
    match b with
    | Data (d, _) ->
      let _, cs = DMap.find d ctx.ds in
      let ptls = List.map (fun cs -> CMap.find c ctx.cs) cs in
      List.fold_left2
        (fun (eqns, map) ptl c ->
          let (ctx, args), tl =
            fold_ptl
              (fun (ctx, acc) a x ptl ->
                let y = V.freshen x in
                let ctx = { ctx with vs = VMap.add y a ctx.vs } in
                let ptl = subst_ptl x ptl (Var y) in
                ((ctx, Var y :: acc), ptl))
              (ctx, []) ptl
          in
          let (ctx, args), targ =
            fold_tl
              (fun (ctx, acc) a x tl ->
                let y = V.freshen x in
                let ctx = { ctx with vs = VMap.add y a ctx.vs } in
                let tl = subst_tl x tl (Var y) in
                ((ctx, Var y :: acc), tl))
              (ctx, []) tl
          in
          let c = Cons (c, List.rev args) in
          let a = subst x a c in
          let ctx = subst_ctx x ctx c in
          let prbm = prbm_subst ctx x prbm c in
          let prbm =
            { prbm with
              Var.global = Var.Eq (env, b, targ, Type s) :: prbm.Var.global
            }
          in
          check_prbm ctx env eqns map prbm a)
        (eqns, map) ptls cs
    | _ -> failwith "check_prbm")
  | (es, [], rhs) :: _ ->
    let es = prbm.global @ es in
    let vmap = Var.unify es in
    let a = msubst vmap a in
    let ctx = msubst_ctx vmap ctx in
    let rhs =
      match rhs with
      | Some m -> msubst vmap m
      | None -> failwith "check_prbm"
    in
    check_tm ctx env eqns map rhs a
  | (es, ps, rhs) :: clause -> (
    let a = whnf rd_all env a in
    match (a, ps) with
    | Pi (s, a, true, abs), _ ->
      let x = V.mk "" in
      let clause = (es, PVar x :: ps, rhs) :: clause in
      let prbm = { prbm with clause } in
      check_prbm ctx env eqns map prbm (Pi (s, a, false, abs))
    | Pi (_, a, false, abs), p :: ps ->
      let x, b = unbind_tm abs in
      let ctx = { ctx with vs = VMap.add x a ctx.vs } in
      let prbm = prbm_add env prbm x a in
      check_prbm ctx env eqns map prbm b
    | _ -> failwith "check_prbm")

and prbm_add env prbm x a =
  let rec aux p =
    match p with
    | PVar x -> Var x
    | PCons (c, ps) -> Cons (c, List.map aux ps)
    | PAbsurd -> Absurd
  in
  match prbm.clause with
  | [] -> prbm
  | (es, p :: ps, rhs) :: clause ->
    let prbm = prbm_add env { prbm with clause } x a in
    let clause =
      (Var.Eq (env, Var x, aux p, a) :: es, ps, rhs) :: prbm.clause
    in
    { prbm with clause }
  | _ -> failwith "prbm_add"

and prbm_subst ctx x prbm m =
  match prbm.clause with
  | [] -> prbm
  | (es, ps, rhs) :: clause -> (
    let prbm = prbm_subst ctx x { prbm with clause } m in
    let opt =
      List.fold_left
        (fun acc (Var.Eq (env, l, r, a)) ->
          match acc with
          | Some acc -> (
            let l = subst x l m in
            let r = subst x r m in
            let a = subst x a m in
            match p_simpl ctx env l r a with
            | Some es -> Some (acc @ es)
            | None -> None)
          | None -> None)
        (Some []) es
    in
    match opt with
    | Some es -> { prbm with clause = (es, ps, rhs) :: prbm.clause }
    | None -> prbm)

and p_simpl ctx env m n a =
  let m = whnf rd_all env m in
  let n = whnf rd_all env n in
  match (m, n) with
  | Cons (c1, xs), Cons (c2, ys) ->
    if C.equal c1 c2 then
      let a = whnf rd_all env a in
      match a with
      | Data (d, ms) ->
        let ptl = CMap.find c1 ctx.cs in
        ps_simpl_ptl ctx env xs ys ptl
      | _ -> None
    else
      None
  | _ -> Some [ Var.Eq (env, m, n, a) ]

and ps_simpl_tl ctx env ms ns tl =
  match (ms, ns, tl) with
  | m :: ms, n :: ns, TBind (a, _, abs) -> (
    let opt1 = p_simpl ctx env m n a in
    let x, tl = unbind_tl abs in
    let tl = subst_tl x tl m in
    let opt2 = ps_simpl_tl ctx env ms ns tl in
    match (opt1, opt2) with
    | Some es1, Some es2 -> Some (es1 @ es2)
    | _ -> None)
  | [], [], TBase _ -> Some []
  | _ -> None

and ps_simpl_ptl ctx env ms ns ptl =
  match (ms, ns, ptl) with
  | m :: ms, n :: ns, PBind (a, _, abs) -> (
    let opt1 = p_simpl ctx env m n a in
    let x, ptl = unbind_ptl abs in
    let ptl = subst_ptl x ptl m in
    let opt2 = ps_simpl_ptl ctx env ms ns ptl in
    match (opt1, opt2) with
    | Some es1, Some es2 -> Some (es1 @ es2)
    | _ -> None)
  | ms, ns, PBase tl -> ps_simpl_tl ctx env ms ns tl
  | _ -> None