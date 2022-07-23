open Fmt
open Names
open Syntax1
open Pprint1
open Equality2
open Unify2

type ctx =
  { vs : Syntax2.tm VMap.t
  ; ds : (Syntax2.ptl * C.t list) DMap.t
  ; cs : Syntax2.ptl CMap.t
  }

let add_v x a ctx = { ctx with vs = VMap.add x a ctx.vs }
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
  let open Pprint2 in
  let aux fmt vs =
    VMap.iter (fun x a -> pf fmt "@[%a :@;<1 2>%a@]@;<1 2>" V.pp x pp_tm a) vs
  in
  pf fmt "@[<v 0>vs={@;<1 2>%a}@]" aux vs

let pp_ds fmt ds =
  let open Pprint2 in
  let aux fmt ds =
    DMap.iter
      (fun d (ptl, _) -> pf fmt "@[%a : %a@]@;<1 2>" D.pp d pp_ptl ptl)
      ds
  in
  pf fmt "@[<v 0>ds={@;<1 2>%a}@]" aux ds

let pp_cs fmt cs =
  let open Pprint2 in
  let aux fmt cs =
    CMap.iter (fun c ptl -> pf fmt "@[%a : %a@]@;<1 2>" C.pp c pp_ptl ptl) cs
  in
  pf fmt "@[<v 0>cs={@;<1 2>%a}@]" aux cs

let pp_ctx fmt ctx =
  pf fmt "@[<v 0>ctx{@;<1 2>%a@;<1 2>%a@;<1 2>%a}@]" pp_vs ctx.vs pp_ds ctx.ds
    pp_cs ctx.cs

let msubst_ctx map ctx =
  let vs = VMap.map (fun a -> UVar.msubst_tm map a) ctx.vs in
  { ctx with vs }

let subst_ctx x ctx m =
  let ctx = { ctx with vs = VMap.remove x ctx.vs } in
  msubst_ctx (VMap.singleton x m) ctx

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Syntax2.Var (fst x)) in
  (Syntax2.Meta (x, xs), x)

let assert_equal env eqns map m n =
  if equal rd_all env m n then
    (eqns, map)
  else
    (UMeta.Eq (env, m, n) :: eqns, map)

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

let rec ps_of_tl tl =
  let open Syntax2 in
  match tl with
  | TBase _ -> []
  | TBind (_, _, abs) ->
    let x, tl = unbind_tl abs in
    let ps = ps_of_tl tl in
    PVar x :: ps

let rec ps_of_ptl ptl =
  let open Syntax2 in
  match ptl with
  | PBase tl -> ps_of_tl tl
  | PBind (_, abs) ->
    let _, ptl = unbind_ptl abs in
    ps_of_ptl ptl

let trans12_sort s =
  match s with
  | U -> Syntax2.U
  | L -> Syntax2.L

let rec infer_sort ctx env eqns map a =
  let srt, a_elab, eqns, map = infer_tm ctx env eqns map a in
  let srt = UMeta.resolve_tm map srt in
  match whnf rd_all env srt with
  | Syntax2.Type s -> (s, a_elab, eqns, map)
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a Pprint2.pp_tm srt

and infer_tm ctx env eqns map m =
  match m with
  | Ann (a, m) -> (
    let _, a_elab, eqns, map = infer_sort ctx env eqns map a in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let m_elab, eqns, map = check_tm ctx env eqns map (Let (m, abs)) a_elab in
      Syntax2.(a_elab, Ann (a_elab, m_elab), eqns, map)
    | _ ->
      let m_elab, eqns, map = check_tm ctx env eqns map m a_elab in
      (a_elab, m_elab, eqns, map))
  | Meta (x, xs) -> (
    let xs_elab, eqns, map =
      List.fold_right
        (fun x (acc, eqns, map) ->
          let _, x_elab, eqns, map = infer_tm ctx env eqns map x in
          (x_elab :: acc, eqns, map))
        xs ([], eqns, map)
    in
    try
      let a_elab = find_m x map in
      Syntax2.(a_elab, Meta (x, xs_elab), eqns, map)
    with
    | _ ->
      let meta, _ = meta_mk ctx in
      Syntax2.(meta, Meta (x, xs_elab), eqns, map))
  | Type s -> Syntax2.(Type U, Type (trans12_sort s), eqns, map)
  | Var x -> Syntax2.(find_v x ctx, Var x, eqns, map)
  | Pi (s, a, impl, abs) ->
    let s_elab = trans12_sort s in
    let x, b = unbind_tm abs in
    let _, a_elab, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a_elab ctx in
    let _, b_elab, eqns, map = infer_sort ctx env eqns map b in
    Syntax2.(Type s_elab, Pi (s_elab, a_elab, impl, bind_tm x b_elab), eqns, map)
  | Fun (a_opt, cls) -> (
    match a_opt with
    | Some a ->
      let _, a_elab, eqns, map = infer_sort ctx env eqns map a in
      let m_elab, eqns, map =
        check_tm ctx env eqns map (Fun (a_opt, cls)) a_elab
      in
      (a_elab, m_elab, eqns, map)
    | None -> failwith "infer_tm_Fun")
  | App (m, n) -> (
    let a, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Syntax2.Pi (_, a, impl, abs) ->
      if impl then
        let meta, meta_x = meta_mk ctx in
        let b = Syntax2.asubst_tm abs meta in
        let z = V.blank () in
        let map = add_m meta_x a map in
        let ctx = add_v z b ctx in
        let res, res_elab, eqns, map =
          infer_tm ctx env eqns map (App (Var z, n))
        in
        match res_elab with
        | Syntax2.(App (Var z_elab, n_elab)) when V.equal z_elab z ->
          Syntax2.(res, App (App (m_elab, meta), n_elab), eqns, map)
        | _ -> failwith "infer_tm_App"
      else
        let n_elab, eqns, map = check_tm ctx env eqns map n a in
        Syntax2.
          (asubst_tm abs (Ann (a, n_elab)), App (m_elab, n_elab), eqns, map)
    | _ -> failwith "infer_tm_App")
  | Let (m, abs) ->
    let a, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let m = UMeta.resolve_tm map m_elab in
    let a = UMeta.resolve_tm map a in
    let x, n = unbind_tm abs in
    let ctx = add_v x a ctx in
    let env = VMap.add x m env in
    let res, res_elab, eqns, map = infer_tm ctx env eqns map n in
    Syntax2.(res, Let (m_elab, bind_tm x res_elab), eqns, map)
  | Data (d, ms) -> (
    let ptl, _ = find_d d ctx in
    try
      let a, ms_elab, eqns, map = check_ptl ctx env eqns map ms ptl in
      Syntax2.(a, Data (d, ms_elab), eqns, map)
    with
    | _ -> failwith "infer_tm_Data")
  | Cons (c, ms) -> (
    let ptl = find_c c ctx in
    try
      let a, ms_elab, eqns, map = check_ptl ctx env eqns map ms ptl in
      Syntax2.(a, Cons (c, ms_elab), eqns, map)
    with
    | _ -> failwith "infer_tm_Cons")
  | Match (ms, cls) ->
    let ms_ty, ms_elab, eqns, map =
      List.fold_left
        (fun (ms_ty, ms_elab, eqns, map) m ->
          let m_ty, m_elab, eqns, map = infer_tm ctx env eqns map m in
          (m_ty :: ms_ty, m_elab :: ms_elab, eqns, map))
        ([], [], eqns, map) ms
    in
    let meta, meta_x = meta_mk ctx in
    let a =
      List.fold_left
        (fun acc m_ty ->
          Syntax2.(Pi (L, m_ty, false, bind_tm (V.blank ()) acc)))
        meta ms_ty
    in
    let prbm = UVar.prbm_of_cls cls in
    let ct, eqns, map = check_prbm ctx env eqns map prbm a in
    Syntax2.(UMeta.resolve_tm map meta, mkApps ct (List.rev ms_elab), eqns, map)
  | If (m, tt, ff) -> (
    let a, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Syntax2.Data (d, _) ->
      let _, cs = find_d d ctx in
      if List.length cs = 2 then
        let ptls = List.map (fun c -> find_c c ctx) cs in
        let tt_ty, tt_elab, eqns, map = infer_tm ctx env eqns map tt in
        let ff_ty, ff_elab, eqns, map = infer_tm ctx env eqns map ff in
        let eqns, map = assert_equal env eqns map tt_ty ff_ty in
        let mot = Syntax2.(Pi (L, a, false, bind_tm (V.blank ()) tt_ty)) in
        let ps =
          List.map2 (fun c ptl -> Syntax2.PCons (c, ps_of_ptl ptl)) cs ptls
        in
        let cls =
          List.map2
            (fun p m -> Syntax2.(Cl (bindp_tm p m)))
            ps [ tt_elab; ff_elab ]
        in
        Syntax2.(tt_ty, Case (m_elab, mot, cls), eqns, map)
      else
        failwith "infer_tm_If"
    | _ -> failwith "infer_tm_If")
  | Main -> Syntax2.(Type L, Main, eqns, map)
  | Proto -> Syntax2.(Type U, Proto, eqns, map)
  | End -> Syntax2.(Proto, End, eqns, map)
  | Act (r, a, abs) ->
    let s, a_elab, eqns, map = infer_sort ctx env eqns map a in
    let x, b = unbind_tm abs in
    let ctx = add_v x a_elab ctx in
    let b_elab, eqns, amp = check_tm ctx env eqns map b Syntax2.Proto in
    Syntax2.(Proto, Act (r, s, a_elab, bind_tm x b_elab), eqns, map)
  | Ch (r, m) ->
    let m_elab, eqns, map = check_tm ctx env eqns map m Syntax2.Proto in
    Syntax2.(Type L, Ch (r, m_elab), eqns, map)
  | Fork (a, m, abs) -> (
    let _, a_elab, eqns, map = infer_sort ctx env eqns map a in
    let a_elab = UMeta.resolve_tm map a_elab in
    match a_elab with
    | Syntax2.Ch (r, a) ->
      let x, n = unbind_tm abs in
      let m_elab, eqns, map = check_tm ctx env eqns map m Syntax2.Main in
      let unit = Syntax2.Data (Prelude.unit_d, []) in
      let ctx = add_v x (Syntax2.Ch (r, a)) ctx in
      let n_elab, eqns, map = check_tm ctx env eqns map n unit in
      let a = Syntax2.Ch (not r, a) in
      Syntax2.
        ( Data (Prelude.tnsr_d, [ a; Main ])
        , Fork (a_elab, m_elab, bind_tm x n_elab)
        , eqns
        , map )
    | _ -> failwith "infer_tm_Fork")
  | Send m -> (
    let a, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Syntax2.Ch (r1, Act (r2, _, a, abs)) when r1 <> r2 = true ->
      let x, b = Syntax2.unbind_tm abs in
      let abs = Syntax2.(bind_tm x (Ch (r1, b))) in
      Syntax2.(Pi (L, a, false, abs), Send m_elab, eqns, map)
    | _ -> failwith "infer_tm_Send")
  | Recv m -> (
    let a, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Syntax2.Ch (r1, Act (r2, s, a, abs)) when r1 <> r2 = false -> (
      let x, b = Syntax2.unbind_tm abs in
      match s with
      | Syntax2.U ->
        let abs = Syntax2.(bind_tm x (Ch (r1, b))) in
        Syntax2.
          ( Data (Prelude.sig_d, [ a; Lam (U, abs) ])
          , Recv (s, m_elab)
          , eqns
          , map )
      | Syntax2.L ->
        Syntax2.
          (Data (Prelude.tnsr_d, [ a; Ch (r1, b) ]), Recv (s, m_elab), eqns, map)
      )
    | _ -> failwith "infer_tm_Recv")
  | Close m -> (
    let a, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Syntax2.(Ch (_, End)) ->
      Syntax2.(Data (Prelude.unit_d, []), Close m_elab, eqns, map)
    | _ -> failwith "infer_tm_Close")

and check_ptl ctx env eqns map ms ptl =
  match (ms, ptl) with
  | m :: ms, Syntax2.PBind (a, abs) ->
    let m_elab, eqns, map = check_tm ctx env eqns map m a in
    let a, ms_elab, eqns, map =
      check_ptl ctx env eqns map ms Syntax2.(asubst_ptl abs (Ann (a, m_elab)))
    in
    (a, m_elab :: ms_elab, eqns, map)
  | ms, Syntax2.PBase tl -> check_tl ctx env eqns map ms tl
  | _ -> failwith "check_ptl"

and check_tl ctx env eqns map ms tl =
  match (ms, tl) with
  | m :: ms, Syntax2.TBind (a, impl, abs) ->
    if impl then
      let meta, meta_x = meta_mk ctx in
      let map = add_m meta_x a map in
      let a, ms_elab, eqns, map =
        check_tl ctx env eqns map (m :: ms) Syntax2.(asubst_tl abs meta)
      in
      (a, meta :: ms_elab, eqns, map)
    else
      let m_elab, eqns, map = check_tm ctx env eqns map m a in
      let a, ms_elab, eqns, map =
        check_tl ctx env eqns map ms Syntax2.(asubst_tl abs (Ann (a, m_elab)))
      in
      (a, m_elab :: ms_elab, eqns, map)
  | [], Syntax2.TBase a -> (a, [], eqns, map)
  | _ -> failwith "check_tl"

and check_tm ctx env eqns map m a =
  match m with
  | Meta (x, xs) ->
    let xs_elab, eqns, map =
      List.fold_right
        (fun x (acc, eqns, map) ->
          let _, x_elab, eqns, map = infer_tm ctx env eqns map x in
          (x_elab :: acc, eqns, map))
        xs ([], eqns, map)
    in
    Syntax2.(Meta (x, xs_elab), eqns, add_m x a map)
  | Fun (b_opt, abs) ->
    let eqns, map =
      match b_opt with
      | Some b ->
        let _, b_elab, eqns, map = infer_sort ctx env eqns map b in
        assert_equal env eqns map a b_elab
      | None -> (eqns, map)
    in
    let x, cls = unbind_cls abs in
    let ctx = add_v x a ctx in
    let prbm = UVar.prbm_of_cls cls in
    let ct, eqns, map = check_prbm ctx env eqns map prbm a in
    if occurs_cls x cls then
      Syntax2.(Fix (a, bind_tm x ct), eqns, map)
    else
      (ct, eqns, map)
  | Let (m, abs) ->
    let m_ty, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let m_ty = UMeta.resolve_tm map m_ty in
    let m_elab = UMeta.resolve_tm map m_elab in
    let x, n = unbind_tm abs in
    let ctx = add_v x m_ty ctx in
    let env = VMap.add x m_elab env in
    let n_elab, eqns, map = check_tm ctx env eqns map n a in
    Syntax2.(Let (m_elab, bind_tm x n_elab), eqns, map)
  | Cons (c, ms) -> (
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Syntax2.Data (_, ns) ->
      let ptl =
        List.fold_left
          (fun ptl n ->
            match ptl with
            | Syntax2.PBind (a, abs) -> Syntax2.(asubst_ptl abs (Ann (a, n)))
            | Syntax2.PBase _ -> ptl)
          (find_c c ctx) ns
      in
      let b, ms_elab, eqns, map = check_ptl ctx env eqns map ms ptl in
      Syntax2.(Cons (c, ms_elab), eqns, map)
    | _ ->
      let b, m_elab, eqns, map = infer_tm ctx env eqns map m in
      let eqns, map = assert_equal env eqns map a b in
      (m_elab, eqns, map))
  | Match (ms, cls) ->
    let ms_ty, ms_elab, eqns, map =
      List.fold_left
        (fun (ms_ty, ms_elab, eqns, map) m ->
          let m_ty, m_elab, eqns, map = infer_tm ctx env eqns map m in
          (m_ty :: ms_ty, m_elab :: ms_elab, eqns, map))
        ([], [], eqns, map) ms
    in
    let a =
      List.fold_left
        (fun acc m_ty ->
          Syntax2.(Pi (L, m_ty, false, bind_tm (V.blank ()) acc)))
        a ms_ty
    in
    let prbm = UVar.prbm_of_cls cls in
    let ct, eqns, map = check_prbm ctx env eqns map prbm a in
    Syntax2.(mkApps ct (List.rev ms_elab), eqns, map)
  | _ ->
    let b, m_elab, eqns, map = infer_tm ctx env eqns map m in
    let eqns, map = assert_equal env eqns map a b in
    (m_elab, eqns, map)

and check_prbm ctx env eqns map prbm a =
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
    | UVar.Eq (_, Var x, Cons (c, _), a) :: _ -> (x, a)
    | _ :: es -> first_split es
    | [] -> failwith "first_split"
  in
  let rec tl_of_ptl ptl ns =
    match (ptl, ns) with
    | Syntax2.PBind (a, abs), n :: ns ->
      let ptl = Syntax2.(asubst_ptl abs (Ann (a, n))) in
      let tl, ns = tl_of_ptl ptl ns in
      (tl, n :: ns)
    | Syntax2.PBase tl, _ -> (tl, [])
    | _ -> failwith "tl_of_ptl"
  in
  match prbm.clause with
  | [] -> failwith "TODO"
  | (es, ps, rhs) :: _ when is_absurd es rhs -> failwith "TODO"
  | (es, ps, rhs) :: _ when can_split es -> failwith "TODO"
  | (es, [], rhs) :: _ -> failwith "TODO"
  | (es, ps, rhs) :: clause -> failwith "TODO"