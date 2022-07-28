open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

let merge usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some false, Some false -> failwith "merge"
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None)
    usage1 usage2

let refine_equal usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some true, None -> None
      | None, Some true -> None
      | None, None -> None
      | _ -> failwith "equal")
    usage1 usage2

let assert_empty usage =
  if VMap.for_all (fun _ b -> b) usage then
    ()
  else
    failwith "assert_empty"

let remove x usage s =
  match s with
  | U -> usage
  | L ->
    if VMap.exists (fun y _ -> V.equal x y) usage then
      VMap.remove x usage
    else
      failwith "remove(%a)" V.pp x

type ctx =
  { vs : (sort * tm) VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let add_v x s a ctx = { ctx with vs = VMap.add x (s, a) ctx.vs }
let add_d d ptl cs ctx = { ctx with ds = DMap.add d (ptl, cs) ctx.ds }
let add_c c ptl ctx = { ctx with cs = CMap.add c ptl ctx.cs }
let add_m x a map = MMap.add x (None, Some a) map

let find_v x ctx =
  match VMap.find_opt x ctx.vs with
  | Some a -> a
  | None -> failwith "find_v(%a)" V.pp x

let find_d d ctx =
  match DMap.find_opt d ctx.ds with
  | Some res -> res
  | None -> failwith "find_d(%a)" D.pp d

let find_c c ctx =
  match CMap.find_opt c ctx.cs with
  | Some ptl -> ptl
  | None -> failwith "find_c(%a)" C.pp c

let find_m x map =
  match MMap.find_opt x map with
  | Some (_, Some a) -> a
  | _ -> failwith "find_m(%a)" M.pp x

let pp_vs fmt vs =
  let aux fmt vs =
    VMap.iter
      (fun x (s, a) ->
        pf fmt "@[%a :%a@;<1 2>%a@]@;<1 2>" V.pp x pp_sort s pp_tm a)
      vs
  in
  pf fmt "@[<v 0>vs={@;<1 2>%a}@]" aux vs

let pp_ds fmt ds =
  let aux fmt ds =
    DMap.iter
      (fun d (ptl, _) -> pf fmt "@[%a : %a@]@;<1 2>" D.pp d pp_ptl ptl)
      ds
  in
  pf fmt "@[<v 0>ds={@;<1 2>%a}@]" aux ds

let pp_cs fmt cs =
  let aux fmt cs =
    CMap.iter (fun c ptl -> pf fmt "@[%a : %a@]@;<1 2>" C.pp c pp_ptl ptl) cs
  in
  pf fmt "@[<v 0>cs={@;<1 2>%a}@]" aux cs

let pp_ctx fmt ctx =
  pf fmt "@[<v 0>ctx{@;<1 2>%a@;<1 2>%a@;<1 2>%a}@]" pp_vs ctx.vs pp_ds ctx.ds
    pp_cs ctx.cs

let msubst_ctx map ctx =
  let vs = VMap.map (fun (s, a) -> (s, UVar.msubst_tm map a)) ctx.vs in
  { ctx with vs }

let subst_ctx x ctx m =
  let ctx = { ctx with vs = VMap.remove x ctx.vs } in
  msubst_ctx (VMap.singleton x m) ctx

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

let assert_equal env m n =
  if equal rd_all env m n then
    ()
  else
    failwith "assert_equal(%a != %a)" pp_tm m pp_tm n

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

let usage_of_ctx ctx = VMap.map (fun _ -> true) ctx.vs

let rec infer_sort ctx env m =
  let a, usage = infer_tm ctx env m in
  match whnf rd_all env a with
  | Type s ->
    let _ = assert_empty usage in
    s
  | _ -> failwith "infer_sort(%a : %a)" pp_tm m pp_tm a

and infer_tm ctx env m =
  match m with
  | Ann (a, m) -> (
    let _ = infer_sort ctx env a in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let usage = check_tm ctx env (Let (m, abs)) a in
      (a, usage)
    | _ ->
      let ctx = check_tm ctx env m a in
      (a, ctx))
  | Meta _ -> failwith "infer_tm_Meta"
  | Type _ -> (Type U, VMap.empty)
  | Var x -> (
    let s, a = find_v x ctx in
    match s with
    | U -> (a, VMap.empty)
    | L -> (a, VMap.singleton x false))
  | Pi (s, a, abs) ->
    let x, b = unbind_tm abs in
    let t = infer_sort ctx env a in
    let _ = infer_sort (add_v x t a ctx) env b in
    (Type s, VMap.empty)
  | Fun (a_opt, abs) -> (
    match a_opt with
    | Some a ->
      let _ = infer_sort ctx env a in
      let usage = check_tm ctx env (Fun (a_opt, abs)) a in
      (a, usage)
    | None -> failwith "infer_Fun(%a)" pp_tm m)
  | App (m, n) -> (
    let a, usage1 = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (s, a, abs) -> (
      let t = infer_sort ctx env a in
      let usage2 = check_tm ctx env n a in
      match t with
      | U ->
        let _ = assert_empty usage2 in
        (asubst_tm abs (Ann (a, n)), usage1)
      | L -> (asubst_tm abs (Ann (a, n)), merge usage1 usage2))
    | _ -> failwith "infer_App(%a)" pp_tm m)
  | Let (m, abs) -> (
    let a, usage1 = infer_tm ctx env m in
    let s = infer_sort ctx env a in
    let x, n = unbind_tm abs in
    match s with
    | U ->
      let _ = assert_empty usage1 in
      infer_tm (add_v x s a ctx) (VMap.add x m env) n
    | L ->
      let b, usage2 = infer_tm (add_v x s a ctx) env n in
      (b, merge usage1 (remove x usage2 s)))
  | Data (d, ms) ->
    let ptl, _ = find_d d ctx in
    check_ptl ctx env ms ptl
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    check_ptl ctx env ms ptl
  | Absurd -> failwith "infer_Absurd"
  | Match (ms, a, cls) ->
    let ms_ty, usage1 =
      List.fold_left
        (fun (ms_ty, acc) m ->
          let m_ty, usage = infer_tm ctx env m in
          (m_ty :: ms_ty, merge usage acc))
        ([], VMap.empty) ms
    in
    let mot =
      List.fold_left
        (fun acc m_ty -> Pi (L, m_ty, bind_tm (V.blank ()) acc))
        a ms_ty
    in
    let _ = infer_sort ctx env mot in
    let prbm = UVar.prbm_of_cls cls in
    let usage2 = check_prbm ctx env prbm mot in
    (a, merge usage1 usage2)
  | If (m, tt, ff) -> (
    let a, usage1 = infer_tm ctx env m in
    let s = infer_sort ctx env a in
    match (whnf rd_all env a, s) with
    | Data (d, _), U ->
      let _, cs = find_d d ctx in
      if List.length cs = 2 then
        let tt_ty, tt_u = infer_tm ctx env tt in
        let ff_ty, ff_u = infer_tm ctx env ff in
        let _ = assert_equal env tt_ty ff_ty in
        let usage2 = refine_equal tt_u ff_u in
        (tt_ty, merge usage1 usage2)
      else
        failwith "infer_If(%a)" pp_tm m
    | _ -> failwith "infer_If(%a)" pp_tm m)
  | Main -> (Type L, VMap.empty)
  | Proto -> (Type U, VMap.empty)
  | End -> (Proto, VMap.empty)
  | Act (r, a, abs) ->
    let x, b = unbind_tm abs in
    let s = infer_sort ctx env a in
    let usage = check_tm (add_v x s a ctx) env b Proto in
    let _ = assert_empty usage in
    (Proto, VMap.empty)
  | Ch (r, m) ->
    let usage = check_tm ctx env m Proto in
    let _ = assert_empty usage in
    (Type L, VMap.empty)
  | Fork (a, m, abs) -> (
    let _ = infer_sort ctx env a in
    match whnf rd_all env a with
    | Ch (r, a) ->
      let x, n = unbind_tm abs in
      let usage1 = check_tm ctx env a Proto in
      let usage2 = check_tm ctx env m Main in
      let unit = Data (Prelude.unit_d, []) in
      let usage3 = check_tm (add_v x L (Ch (r, a)) ctx) env n unit in
      let usage3 = remove x usage3 L in
      let a = Ch (not r, a) in
      let _ = assert_empty usage1 in
      (Data (Prelude.tnsr_d, [ a; Main ]), merge usage2 usage3)
    | _ -> failwith "infer_Fork(%a)" pp_tm a)
  | Send m -> (
    let a, usage = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 ->
      let x, b = unbind_tm abs in
      let abs = bind_tm x (Ch (r1, b)) in
      (Pi (L, a, abs), usage)
    | _ -> failwith "infer_Send(%a)" pp_tm a)
  | Recv m -> (
    let a, usage = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 = r2 -> (
      let x, b = unbind_tm abs in
      let s = infer_sort ctx env a in
      match s with
      | U -> (Data (Prelude.sig_d, [ a; lam x (Ch (r1, b)) ]), usage)
      | L -> (Data (Prelude.tnsr_d, [ a; Ch (r1, b) ]), usage))
    | _ -> failwith "infer_Recv(%a)" pp_tm a)
  | Close m -> (
    let a, usage = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (_, End) -> (Data (Prelude.unit_d, []), usage)
    | _ -> failwith "infer_Close(%a)" pp_tm a)

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) -> (
    let s = infer_sort ctx env a in
    let usage1 = check_tm ctx env m a in
    let a, usage2 = check_ptl ctx env ms (asubst_ptl abs (Ann (a, m))) in
    match s with
    | U ->
      let _ = assert_empty usage1 in
      (a, usage2)
    | L -> (a, merge usage1 usage2))
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (a, abs) -> (
    let s = infer_sort ctx env a in
    let usage1 = check_tm ctx env m a in
    let a, usage2 = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    match s with
    | U ->
      let _ = assert_empty usage1 in
      (a, usage2)
    | L -> (a, merge usage1 usage2))
  | [], TBase a ->
    let _ = infer_sort ctx env a in
    (a, VMap.empty)
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a =
  match m with
  | Fun (b_opt, abs) ->
    let s =
      match b_opt with
      | Some b ->
        let s = infer_sort ctx env b in
        let _ = assert_equal env a b in
        s
      | None -> infer_sort ctx env a
    in
    let x, cls = unbind_cls abs in
    let prbm = UVar.prbm_of_cls cls in
    let ctx =
      match s with
      | U -> add_v x s a ctx
      | L -> ctx
    in
    check_prbm ctx env prbm a
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, usage = infer_tm ctx env (Let (m, abs)) in
    let _ = assert_equal env a b in
    usage
  | Cons (c, ms) -> (
    match whnf rd_all env a with
    | Data (_, ns) ->
      let ptl = find_c c ctx in
      let ptl =
        List.fold_left
          (fun ptl n ->
            match ptl with
            | PBind (a, abs) -> asubst_ptl abs (Ann (a, n))
            | PBase _ -> ptl)
          ptl ns
      in
      let b, usage = check_ptl ctx env ms ptl in
      let _ = assert_equal env a b in
      usage
    | _ ->
      let b, usage = infer_tm ctx env m in
      let _ = assert_equal env a b in
      usage)
  | Match (ms, b, cls) ->
    let ms_ty, usage1 =
      List.fold_left
        (fun (ms_ty, acc) m ->
          let m_ty, usage = infer_tm ctx env m in
          (m_ty :: ms_ty, merge usage acc))
        ([], VMap.empty) ms
    in
    let mot =
      List.fold_left
        (fun acc m_ty -> Pi (L, m_ty, bind_tm (V.blank ()) acc))
        b ms_ty
    in
    let _ = infer_sort ctx env mot in
    let prbm = UVar.prbm_of_cls cls in
    let usage2 = check_prbm ctx env prbm mot in
    let _ = assert_equal env a b in
    merge usage1 usage2
  | _ ->
    let b, usage = infer_tm ctx env m in
    let _ = assert_equal env a b in
    usage

and check_prbm ctx env prbm a =
  let rec is_absurd es rhs =
    match (es, rhs) with
    | UVar.Eq (_, Var _, Absurd, _) :: _, None -> true
    | UVar.Eq (_, Var _, Absurd, _) :: _, Some _ -> failwith "is_absurd"
    | _ :: es, _ -> is_absurd es rhs
    | [], _ -> false
  in
  let rec get_absurd es =
    match es with
    | UVar.Eq (_, Var _, Absurd, a) :: _ -> a
    | _ :: es -> get_absurd es
    | [] -> failwith "get_absurd"
  in
  let rec can_split es =
    match es with
    | UVar.Eq (_, Var _, Cons (_, _), _) :: _ -> true
    | _ :: es -> can_split es
    | [] -> false
  in
  let rec first_split es =
    match es with
    | UVar.Eq (_, Var x, Cons (c, ms), a) :: _ -> (x, a)
    | _ :: es -> first_split es
    | [] -> failwith "first_split"
  in
  let rec tl_of_ptl ptl ns =
    match (ptl, ns) with
    | PBind (a, abs), n :: ns ->
      let ptl = asubst_ptl abs (Ann (a, n)) in
      let tl, ns = tl_of_ptl ptl ns in
      (tl, n :: ns)
    | PBase tl, _ -> (tl, [])
    | _ -> failwith "tl_of_ptl"
  in
  match prbm.clause with
  | [] -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      usage_of_ctx ctx
    else
      match whnf rd_all env a with
      | Pi (_, a, _) -> (
        match whnf rd_all env a with
        | Data (d, _) ->
          let _, cs = find_d d ctx in
          if cs <> [] then
            failwith "check_Empty"
          else
            usage_of_ctx ctx
        | _ -> failwith "check_Empty")
      | _ -> failwith "check_Empty")
  | (es, ps, rhs) :: _ when is_absurd es rhs -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      usage_of_ctx ctx
    else
      let a = get_absurd es in
      let _ = infer_sort ctx env a in
      match whnf rd_all env a with
      | Data (d, _) ->
        let _, cs = find_d d ctx in
        if cs <> [] then
          failwith "check_Absurd"
        else
          usage_of_ctx ctx
      | _ -> failwith "check_Absurd")
  | (es, ps, rhs) :: _ when can_split es -> failwith "TODO"
  | (es, [], rhs) :: _ -> failwith "TODO"
  | (es, ps, rhs) :: clause -> (
    let a = whnf rd_all env a in
    match (a, ps) with
    | Pi (s, a, abs), p :: ps -> (
      let x, b = unbind_tm abs in
      let t = infer_sort ctx env a in
      let ctx = add_v x t a ctx in
      let prbm = prbm_add ctx env prbm x a in
      let usage = check_prbm ctx env prbm b in
      let usage = remove x usage t in
      match s with
      | U ->
        let _ = assert_empty usage in
        VMap.empty
      | L -> usage)
    | _ -> failwith "check_Intro")

and prbm_add ctx env prbm x a =
  let rec tm_of_p p =
    match p with
    | PVar x -> Var x
    | PCons (c, ps) ->
      let ptl = find_c c ctx in
      let ps = ps_of_ptl ps ptl in
      let ps = List.map tm_of_p ps in
      Cons (c, ps)
    | PAbsurd -> Absurd
  and ps_of_ptl ps ptl =
    match ptl with
    | PBase tl -> ps_of_tl ps tl
    | PBind (_, abs) ->
      let _, ptl = unbind_ptl abs in
      PVar (V.blank ()) :: ps_of_ptl ps ptl
  and ps_of_tl ps tl =
    match tl with
    | TBase _ -> ps
    | TBind (_, abs) -> (
      let _, tl = unbind_tl abs in
      match ps with
      | p :: ps -> p :: ps_of_tl ps tl
      | _ -> failwith "ps_of_tl")
  in
  match prbm.clause with
  | [] -> prbm
  | (es, p :: ps, rhs) :: clause ->
    let prbm = prbm_add ctx env { prbm with clause } x a in
    let clause =
      (UVar.Eq (env, Var x, tm_of_p p, a) :: es, ps, rhs) :: prbm.clause
    in
    { prbm with clause }
  | _ -> failwith "prbm_add"