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

let rec aeq m1 m2 =
  if m1 == m2 then
    true
  else
    match (m1, m2) with
    | Ann (a1, m1), Ann (a2, m2) -> aeq a1 a2 && aeq m1 m2
    | Meta (x1, _), Meta (x2, _) -> V.equal x1 x2
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (s1, a1, _, abs1), Pi (s2, a2, _, abs2) ->
      s1 = s2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
      Option.equal aeq a1_opt a2_opt
      && equal_abs
           (fun cls1 cls2 ->
             List.equal
               (fun (Cl pabs1) (Cl pabs2) ->
                 equal_pabs (Option.equal aeq) pabs1 pabs2)
               cls1 cls2)
           abs1 abs2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (m1, abs1), Let (m2, abs2) -> aeq m1 m2 && equal_abs aeq abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) -> D.equal d1 d2 && List.equal aeq ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) -> C.equal c1 c2 && List.equal aeq ms1 ms2
    | Match (ms1, cls1), Match (ms2, cls2) ->
      List.equal aeq ms1 ms2
      && List.equal
           (fun (Cl pabs1) (Cl pabs2) ->
             equal_pabs (Option.equal aeq) pabs1 pabs2)
           cls1 cls2
    | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
      aeq m1 m2 && aeq tt1 tt2 && aeq ff1 ff2
    | Main, Main -> true
    | Proto, Proto -> true
    | End, End -> true
    | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
      r1 = r2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Ch (r1, a1), Ch (r2, a2) -> r1 = r2 && aeq a1 a2
    | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
      aeq a1 a2 && aeq m1 m2 && equal_abs aeq abs1 abs2
    | Send m1, Send m2 -> aeq m1 m2
    | Recv m1, Recv m2 -> aeq m1 m2
    | Close m1, Close m2 -> aeq m1 m2
    | _ -> false

let rec equal rds env m1 m2 =
  if aeq m1 m2 then
    true
  else
    let m1 = whnf rds env m1 in
    let m2 = whnf rds env m2 in
    match (m1, m2) with
    | Ann (a1, m1), Ann (a2, m2) -> equal rds env a1 a2 && equal rds env m1 m2
    | Meta (x1, _), Meta (x2, _) -> V.equal x1 x2
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (s1, a1, _, abs1), Pi (s2, a2, _, abs2) ->
      s1 = s2 && equal rds env a1 a2 && equal_abs (equal rds env) abs1 abs2
    | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
      Option.equal (equal rds env) a1_opt a2_opt
      && equal_abs
           (fun cls1 cls2 ->
             List.equal
               (fun (Cl pabs1) (Cl pabs2) ->
                 equal_pabs (Option.equal (equal rds env)) pabs1 pabs2)
               cls1 cls2)
           abs1 abs2
    | App (m1, n1), App (m2, n2) -> equal rds env m1 m2 && equal rds env n1 n2
    | Let (m1, abs1), Let (m2, abs2) ->
      equal rds env m1 m2 && equal_abs (equal rds env) abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) ->
      D.equal d1 d2 && List.equal (equal rds env) ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
      C.equal c1 c2 && List.equal (equal rds env) ms1 ms2
    | Match (ms1, cls1), Match (ms2, cls2) ->
      List.equal (equal rds env) ms1 ms2
      && List.equal
           (fun (Cl pabs1) (Cl pabs2) ->
             equal_pabs (Option.equal (equal rds env)) pabs1 pabs2)
           cls1 cls2
    | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
      equal rds env m1 m2 && equal rds env tt1 tt2 && equal rds env ff1 ff2
    | Main, Main -> true
    | Proto, Proto -> true
    | End, End -> true
    | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
      r1 = r2 && equal rds env a1 a2 && equal_abs (equal rds env) abs1 abs2
    | Ch (r1, a1), Ch (r2, a2) -> r1 = r2 && equal rds env a1 a2
    | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
      equal rds env a1 a2 && equal rds env m1 m2
      && equal_abs (equal rds env) abs1 abs2
    | Send m1, Send m2 -> equal rds env m1 m2
    | Recv m1, Recv m2 -> equal rds env m1 m2
    | Close m1, Close m2 -> equal rds env m1 m2
    | _ -> false