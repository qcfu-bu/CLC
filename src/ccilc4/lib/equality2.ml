open Fmt
open Names
open Syntax2

type rd =
  | Beta
  | Delta
  | Zeta
  | Iota
  | Rec

let rd_all = [ Beta; Delta; Zeta; Iota; Rec ]
let has_rd rds rd = List.exists (( = ) rd) rds

let rec whnf rds env m =
  match m with
  | Ann (a, m) -> (
    let m = whnf rds env m in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      whnf rds env (Let (m, abs))
    | Case (m, a, cls) ->
      let cls =
        List.map
          (fun (Cl pabs) ->
            let p, rhs = unbindp_tm pabs in
            let rhs = Ann (a, rhs) in
            Cl (bindp_tm p rhs))
          cls
      in
      whnf rds env (Case (m, a, cls))
    | _ -> m)
  | Var x ->
    if has_rd rds Delta then
      match VMap.find_opt x env with
      | Some m -> whnf rds env m
      | _ -> Var x
    else
      Var x
  | App (m, n) -> (
    let m = whnf rds env m in
    let n = whnf rds env n in
    match m with
    | Lam (_, abs) ->
      if has_rd rds Beta then
        whnf rds env (asubst_tm abs n)
      else
        App (m, n)
    | Fix (_, abs) ->
      if has_rd rds Rec then
        whnf rds env (App (asubst_tm abs m, n))
      else
        App (m, n)
    | _ -> App (m, n))
  | Let (m, abs) ->
    let m = whnf rds env m in
    if has_rd rds Zeta then
      let x, n = unbind_tm abs in
      whnf rds (VMap.add x m env) n
    else
      Let (m, abs)
  | Case (m, a, cls) ->
    let m = whnf rds env m in
    let a = whnf rds env a in
    if has_rd rds Iota then
      match match_cls cls m with
      | Some m -> whnf rds env m
      | _ -> Case (m, a, cls)
    else
      Case (m, a, cls)
  | Ch (r, m) -> Ch (r, whnf rds env m)
  | _ -> m

and match_cls cls m =
  List.fold_left
    (fun acc (Cl pabs) ->
      match acc with
      | Some _ -> acc
      | None -> (
        try Some (asubstp_tm pabs m) with
        | _ -> None))
    None cls

let rec eval rds env dcls =
  match dcls with
  | [] -> []
  | DTm (x, a, m) :: dcls ->
    let a = whnf rds env a in
    let m = whnf rds env m in
    let env = VMap.add x m env in
    let dcls = eval rds env dcls in
    DTm (x, a, m) :: dcls
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
    | Pi (s1, a1, _, abs1), Pi (s2, a2, _, abs2) ->
      s1 = s2 && aeq a1 a2 && equal_abs aeq abs1 abs2
    | Fix (a1, abs1), Fix (a2, abs2) -> aeq a1 a2 && equal_abs aeq abs1 abs2
    | Lam (s1, abs1), Lam (s2, abs2) -> s1 = s2 && equal_abs aeq abs1 abs2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (m1, abs1), Let (m2, abs2) -> aeq m1 m2 && equal_abs aeq abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) -> D.equal d1 d2 && List.equal aeq ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) -> C.equal c1 c2 && List.equal aeq ms1 ms2
    | Case (m1, a1, cls1), Case (m2, a2, cls2) ->
      aeq m1 m2 && aeq a1 a2
      && List.equal
           (fun (Cl pabs1) (Cl pabs2) -> equal_pabs aeq pabs1 pabs2)
           cls1 cls2
    | Main, Main -> true
    | Proto, Proto -> true
    | End, End -> true
    | Act (r1, s1, a1, abs1), Act (r2, s2, a2, abs2) ->
      r1 = r2 && s1 = s2 && aeq a1 a2 && equal_abs aeq abs1 abs2
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
    | Pi (s1, a1, _, abs1), Pi (s2, a2, _, abs2) ->
      s1 = s2 && equal rds env a1 a2 && equal_abs (equal rds env) abs1 abs2
    | Fix (a1, abs1), Fix (a2, abs2) ->
      equal rds env a1 a2 && equal_abs (equal rds env) abs1 abs2
    | Lam (s1, abs1), Lam (s2, abs2) ->
      s1 = s2 && equal_abs (equal rds env) abs1 abs2
    | App (m1, n1), App (m2, n2) -> equal rds env m1 m2 && equal rds env n1 n2
    | Let (m1, abs1), Let (m2, abs2) ->
      equal rds env m1 m2 && equal_abs (equal rds env) abs1 abs2
    | Data (d1, ms1), Data (d2, ms2) ->
      D.equal d1 d2 && List.equal (equal rds env) ms1 ms2
    | Cons (c1, ms1), Cons (c2, ms2) ->
      C.equal c1 c2 && List.equal (equal rds env) ms1 ms2
    | Case (m1, a1, cls1), Case (m2, a2, cls2) ->
      equal rds env m1 m2 && equal rds env a1 a2
      && List.equal
           (fun (Cl pabs1) (Cl pabs2) -> equal_pabs (equal rds env) pabs1 pabs2)
           cls1 cls2
    | Main, Main -> true
    | Proto, Proto -> true
    | End, End -> true
    | Act (r1, s1, a1, abs1), Act (r2, s2, a2, abs2) ->
      r1 = r2 && s1 = s2 && equal rds env a1 a2
      && equal_abs (equal rds env) abs1 abs2
    | Ch (r1, a1), Ch (r2, a2) -> r1 = r2 && equal rds env a1 a2
    | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
      equal rds env a1 a2 && equal rds env m1 m2
      && equal_abs (equal rds env) abs1 abs2
    | Send m1, Send m2 -> equal rds env m1 m2
    | Recv m1, Recv m2 -> equal rds env m1 m2
    | Close m1, Close m2 -> equal rds env m1 m2
    | _ -> false