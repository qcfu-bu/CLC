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
  let x = V.mk "" in
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
  let h, _ = unApps m in
  match m with
  | Ann (a, m) -> (
    let _, eqns, map = infer_sort ctx env eqns map a in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let eqns, map = check ctx env eqns map (Let (m, abs)) a in
      (a, eqns, map)
    | _ ->
      let eqns, map = check ctx env eqns map m a in
      (a, eqns, map))
  | Meta (x, xs) -> (
    match VMap.find_opt x ctx.vs with
    | Some a -> (a, eqns, map)
    | None -> (fst (meta_mk ctx), eqns, map))
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
        let m, y = meta_mk ctx in
        let b = subst x b m in
        let z = V.mk "" in
        let ctx = { ctx with vs = VMap.add y a ctx.vs } in
        let ctx = { ctx with vs = VMap.add z b ctx.vs } in
        infer_tm ctx env eqns map (App (Var z, n))
      else
        let x, b = unbind_tm abs in
        let eqns, map = check ctx env eqns map n a in
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
    | _ -> failwith ()
    | _ -> failwith "TODO")

and check = failwith "TODO"
