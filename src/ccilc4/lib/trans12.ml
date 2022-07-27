open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

type t = bool VMap.t

let merge u1 u2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some false, Some false -> failwith "merge"
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None)
    u1 u2

let refine_equal u1 u2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some b1, Some b2 -> Some (b1 && b2)
      | _ -> failwith "equal")
    u1 u2

let assert_empty u =
  if VMap.for_all (fun _ b -> b) u then
    ()
  else
    failwith "assert_empty"

let remove x u s =
  match s with
  | U -> u
  | L ->
    if VMap.exists (fun y _ -> V.equal x y) u then
      VMap.remove x u
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

let assert_equal env u m n =
  if equal rd_all env m n then
    u
  else
    failwith "assert_equal(%a != %a)" pp_tm m pp_tm n

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

let rec infer_sort ctx env m =
  let a, u = infer_tm ctx env m in
  match whnf rd_all env a with
  | Type s ->
    let _ = assert_empty u in
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
      let u = check_tm ctx env (Let (m, abs)) a in
      (a, u)
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
      let u = check_tm ctx env (Fun (a_opt, abs)) a in
      (a, u)
    | None -> failwith "infer_Fun(%a)" pp_tm m)
  | App (m, n) -> (
    let a, u1 = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (s, a, abs) -> (
      let t = infer_sort ctx env a in
      let u2 = check_tm ctx env n a in
      match t with
      | U ->
        let _ = assert_empty u2 in
        (asubst_tm abs (Ann (a, n)), u1)
      | L -> (asubst_tm abs (Ann (a, n)), merge u1 u2))
    | _ -> failwith "infer_App(%a)" pp_tm m)
  | Let (m, abs) -> (
    let a, u1 = infer_tm ctx env m in
    let s = infer_sort ctx env a in
    let x, n = unbind_tm abs in
    match s with
    | U ->
      let _ = assert_empty u1 in
      infer_tm (add_v x s a ctx) (VMap.add x m env) n
    | L ->
      let b, u2 = infer_tm (add_v x s a ctx) env n in
      (b, merge u1 (remove x u2 s)))
  | Data (d, ms) ->
    let ptl, _ = find_d d ctx in
    check_ptl ctx env ms ptl
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    check_ptl ctx env ms ptl
  | Absurd -> failwith "infer_Absurd"
  | Match (ms, a, cls) -> failwith "TODO"
  | If (m, tt, ff) -> (
    let a, u1 = infer_tm ctx env m in
    let s = infer_sort ctx env a in
    match (whnf rd_all env a, s) with
    | Data (d, _), U ->
      let _, cs = find_d d ctx in
      if List.length cs = 2 then
        let tt_ty, tt_u = infer_tm ctx env tt in
        let ff_ty, ff_u = infer_tm ctx env ff in
        let u2 = assert_equal env (refine_equal tt_u ff_u) tt_ty ff_ty in
        (tt_ty, merge u1 u2)
      else
        failwith "infer_If(%a)" pp_tm m
    | _ -> failwith "infer_If(%a)" pp_tm m)
  | Main -> (Type L, VMap.empty)
  | Proto -> (Type U, VMap.empty)
  | End -> (Proto, VMap.empty)
  | Act (r, a, abs) ->
    let x, b = unbind_tm abs in
    let s = infer_sort ctx env a in
    let u = check_tm (add_v x s a ctx) env b Proto in
    let _ = assert_empty u in
    (Proto, VMap.empty)
  | Ch (r, m) ->
    let u = check_tm ctx env m Proto in
    let _ = assert_empty u in
    (Type L, VMap.empty)
  | Fork (a, m, abs) -> (
    let _ = infer_sort ctx env a in
    match whnf rd_all env a with
    | Ch (r, a) ->
      let x, n = unbind_tm abs in
      let u1 = check_tm ctx env a Proto in
      let u2 = check_tm ctx env m Main in
      let unit = Data (Prelude.unit_d, []) in
      let u3 = check_tm (add_v x L (Ch (r, a)) ctx) env n unit in
      let u3 = remove x u3 L in
      let a = Ch (not r, a) in
      let _ = assert_empty u1 in
      (Data (Prelude.tnsr_d, [ a; Main ]), merge u2 u3)
    | _ -> failwith "infer_Fork(%a)" pp_tm a)
  | Send m -> (
    let a, u = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 ->
      let x, b = unbind_tm abs in
      let abs = bind_tm x (Ch (r1, b)) in
      (Pi (L, a, abs), u)
    | _ -> failwith "infer_Send(%a)" pp_tm a)
  | Recv m -> (
    let a, u = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 = r2 -> (
      let x, b = unbind_tm abs in
      let s = infer_sort ctx env a in
      match s with
      | U -> (Data (Prelude.sig_d, [ a; lam x (Ch (r1, b)) ]), u)
      | L -> (Data (Prelude.tnsr_d, [ a; Ch (r1, b) ]), u))
    | _ -> failwith "infer_Recv(%a)" pp_tm a)
  | Close m -> (
    let a, u = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (_, End) -> (Data (Prelude.unit_d, []), u)
    | _ -> failwith "infer_Close(%a)" pp_tm a)

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) -> (
    let s = infer_sort ctx env a in
    let u1 = check_tm ctx env m a in
    let a, u2 = check_ptl ctx env ms (asubst_ptl abs (Ann (a, m))) in
    match s with
    | U ->
      let _ = assert_empty u1 in
      (a, u2)
    | L -> (a, merge u1 u2))
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (a, abs) -> (
    let s = infer_sort ctx env a in
    let u1 = check_tm ctx env m a in
    let a, u2 = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    match s with
    | U ->
      let _ = assert_empty u1 in
      (a, u2)
    | L -> (a, merge u1 u2))
  | [], TBase a ->
    let _ = infer_sort ctx env a in
    (a, VMap.empty)
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a =
  match m with
  | Fun (b_opt, abs) -> failwith "TODO"
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, u = infer_tm ctx env (Let (m, abs)) in
    assert_equal env u a b
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
      let b, u = check_ptl ctx env ms ptl in
      assert_equal env u a b
    | _ ->
      let b, u = infer_tm ctx env m in
      assert_equal env u a b)
  | Match (m, a, cls) -> failwith "TODO"
  | _ ->
    let b, u = infer_tm ctx env m in
    assert_equal env u a b
