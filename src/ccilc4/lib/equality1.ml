open Fmt
open Names
open Syntax1
open Pprint1

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
    | Fun abs -> Fun abs
    | _ -> m)
  | Var x ->
    if List.exists (( = ) Delta) rds then
      match VMap.find_opt x env with
      | Some m -> whnf rds env m
      | _ -> Var x
    else
      Var x
  | App (m, n) -> (
    let m = whnf rds env m in
    let n = whnf rds env n in
    match m with
    | Fun abs ->
      if List.exists (( = ) Beta) rds then
        let cls = asubst_cls abs m in
        match match_cls cls n with
        | Either.Left (Some n) -> whnf rds env n
        | Either.Left None -> App (m, n)
        | Either.Right [] -> App (m, n)
        | Either.Right cls -> Fun (bind_cls (V.blank ()) cls)
      else
        App (m, n)
    | _ -> App (m, n))
  | Let (m, abs) ->
    if List.exists (( = ) Zeta) rds then
      let m = whnf rds env m in
      let x, n = unbind_tm abs in
      whnf rds (VMap.add x m env) n
    else
      Let (m, abs)
  | Match (ms, cls) ->
    let ms = List.map (whnf rds env) ms in
    if List.exists (( = ) Iota) rds then
      let res =
        List.fold_left
          (fun acc m ->
            match acc with
            | Either.Left (Some n) -> Either.Left None
            | Either.Left None -> Either.Left None
            | Either.Right [] -> Either.Right []
            | Either.Right cls -> match_cls cls m)
          (Either.Right cls) ms
      in
      match res with
      | Either.Left (Some n) -> whnf rds env n
      | _ -> Match (ms, cls)
    else
      Match (ms, cls)
  | Ch (r, m) -> Ch (r, whnf rds env m)
  | _ -> m

and match_cls cls (m : tm) =
  match cls with
  | Cl pabs :: cls -> (
    let ps, rhs = unbindp_tm_opt pabs in
    try
      let ps, rhs = substp_tm_opt ps rhs m in
      match ps with
      | [] -> Either.Left rhs
      | _ -> (
        match match_cls cls m with
        | Either.Left rhs -> Either.left rhs
        | Either.Right cls -> Either.Right (Cl (bindp_tm_opt ps rhs) :: cls))
    with
    | _ -> match_cls cls m)
  | [] -> Either.Right []

and match_p map p m =
  match (p, m) with
  | PVar x, _ -> VMap.add x m map
  | PCons (c1, ps), Cons (c2, ms) ->
    if C.equal c1 c2 then
      List.fold_left2 (fun acc p m -> match_p acc p m) map ps ms
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
    let env = VMap.add x (Ann (a, Fun abs)) env in
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
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (s1, a1, abs1), Pi (s2, a2, abs2) ->
      s1 = s2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Fun abs1, Fun abs2 ->
      equal_abs
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
    | Meta (x1, _), Meta (x2, _) -> M.equal x1 x2
    | Type s1, Type s2 -> s1 = s2
    | Var x1, Var x2 -> V.equal x1 x2
    | Pi (s1, a1, abs1), Pi (s2, a2, abs2) ->
      s1 = s2 && equal rds env a1 a2 && equal_abs (equal rds env) abs1 abs2
    | Fun abs1, Fun abs2 ->
      equal_abs
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