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

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

let assert_equal env eqns map m n =
  if equal rd_all env m n then
    (eqns, map)
  else
    (HigherOrder.Eq (env, m, n) :: eqns, map)

let rec infer_sort ctx env eqns map m =
  let a, eqns, map = infer_tm ctx env eqns map m in
  let a = HigherOrder.resolve_tm map a in
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
  | Fun _ -> failwith "TODO"
  | App (m, n) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = HigherOrder.resolve_tm map a in
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
    let m = HigherOrder.resolve_tm map m in
    let a = HigherOrder.resolve_tm map a in
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
  | Match (ms, cls) -> failwith "TODO"
  | If (m, tt, ff) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = HigherOrder.resolve_tm map a in
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
    let a = HigherOrder.resolve_tm map a in
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
    let a = HigherOrder.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 = true ->
      let x, b = unbind_tm abs in
      let abs = bind_tm x (Ch (r1, b)) in
      (Pi (L, a, false, abs), eqns, map)
    | _ -> failwith "infer_tm(%a)" pp_tm m)
  | Recv m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = HigherOrder.resolve_tm map a in
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
    let a = HigherOrder.resolve_tm map a in
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
  | _ -> failwith "TODO"
