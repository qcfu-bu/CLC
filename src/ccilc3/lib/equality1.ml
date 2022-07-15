open Names
open Syntax1

type rd =
  | Beta
  | Delta
  | Zeta
  | Iota

let rd_all = [ Beta; Delta; Zeta; Iota ]

let rec whnf rds env m =
  match m with
  | Ann (a, m) -> (
    let m = whnf rds env m in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      whnf rds env (Let (m, abs))
    | Match (ms, cls) ->
      let cls =
        List.map
          (fun (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (fun m -> Ann (a, m)) m_opt in
            Cl (bindp_tm_opt ps m_opt))
          cls
      in
      whnf rds env (Match (ms, cls))
    | Fun (None, abs) -> Fun (Some a, abs)
    | _ -> m)
  | Var x ->
    if List.exists (( = ) Delta) rds then
      match VMap.find_opt x env with
      | Some m -> whnf rds env m
      | _ -> Var x
    else
      Var x
  | App _ -> (
    let m, sp = unApps m in
    let m = whnf rds env m in
    let sp = List.map (whnf rds env) sp in
    match (m, sp) with
    | Fun (_, abs), _ :: _ ->
      if List.exists (( = ) Iota) rds then
        let x, cls = unbind_cls abs in
        match match_cls cls sp with
        | Some (Some n) -> whnf rds env (subst x n m)
        | _ -> mkApps m sp
      else
        mkApps m sp
    | _ -> mkApps m sp)
  | Let (m, abs) ->
    if List.exists (( = ) Zeta) rds then
      let m = whnf rds env m in
      let x, n = unbind_tm abs in
      whnf rds (VMap.add x m env) n
    else
      Let (m, abs)
  | Match (ms, cls) ->
    if List.exists (( = ) Iota) rds then
      match match_cls cls ms with
      | Some (Some m) -> whnf rds env m
      | _ -> Match (ms, cls)
    else
      Match (ms, cls)
  | Ch (r, m) -> Ch (r, whnf rds env m)
  | Data (d, ms) -> Data (d, List.map (whnf rds env) ms)
  | Cons (c, ms) -> Cons (c, List.map (whnf rds env) ms)
  | _ -> m

and match_cls cls ms =
  List.fold_left
    (fun acc (Cl pabs) ->
      match acc with
      | Some _ -> acc
      | None -> (
        let ps, m_opt = unbindp_tm_opt pabs in
        try
          let vmap =
            List.fold_left2 (fun acc p m -> match_p acc p m) VMap.empty ps ms
          in
          Some (Option.map (msubst vmap) m_opt)
        with
        | _ -> None))
    None cls

and match_p vmap p m =
  match (p, m) with
  | PVar x, _ -> VMap.add x m vmap
  | PCons (c1, ps), Cons (c2, ms) ->
    if C.equal c1 c2 then
      List.fold_left2 (fun acc p m -> match_p acc p m) vmap ps ms
    else
      failwith "match_p"
  | _ -> failwith "match_p"

let rec eval rds env dcls =
  match dcls with
  | [] -> []
  | DTm (x, a_opt, m) :: dcls ->
    let a_opt = Option.map (whnf rds env) a_opt in
    let m = whnf rds env m in
    let env = VMap.add x m env in
    let dcls = eval rds env dcls in
    DTm (x, a_opt, m) :: dcls
  | DFun (x, a, abs) :: dcls ->
    let a = whnf rds env a in
    let env = VMap.add x (Fun (Some a, abs)) env in
    let dcls = eval rds env dcls in
    DFun (x, a, abs) :: dcls
  | DData _ :: dcls -> eval rds env dcls
  | DOpen _ :: dcls -> eval rds env dcls
  | DAxiom (x, a) :: dcls ->
    let a = whnf rds env a in
    let dcls = eval rds env dcls in
    DAxiom (x, a) :: dcls
