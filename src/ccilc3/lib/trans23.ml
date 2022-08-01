open Fmt
open Names
open Syntax2
open Syntax3
open Pprint2

let extend_env local env = List.map fst local @ env

let value_of local env =
  let env1 = List.map snd local in
  let env2 = List.mapi (fun i _ -> Env i) env in
  env1 @ env2

let findi y ls =
  let rec loop i = function
    | [] -> failwith "findi(%a)" V.pp y
    | x :: xs ->
      if V.equal x y then
        i
      else
        loop (i + 1) xs
  in
  loop 0 ls

let trans_p local p v =
  let aux c i = function
    | PVar x -> ([ Mov (x, Proj (v, i)) ], local @ [ (x, Reg x) ])
    | _ -> failwith "trans_p"
  in
  match p with
  | PCons (c, ps) ->
    let _, instr, local =
      List.fold_left
        (fun (i, instr, local) p ->
          let p_instr, local = aux c i p in
          (i + 1, instr @ p_instr, local))
        (0, [], local) ps
    in
    (c, instr, local)
  | _ -> failwith "trans_p"

let rec trans_tm def local env m =
  match m with
  | Type _ -> (def, [], Zero)
  | Var x -> (
    try
      let v = List.find (fun (y, _) -> V.equal x y) local in
      (def, [], snd v)
    with
    | _ -> (def, [], Env (findi x env)))
  | Pi _ -> (def, [], Zero)
  | Fix abs ->
    let f, x, m = unbind_tm_abs abs in
    let def, instr, v =
      trans_tm def [ (x, Reg x) ] (f :: extend_env local env) m
    in
    let name = V.freshen f in
    let tmp = V.blank () in
    let proc = { name; arg = x; body = instr; return = v } in
    (def @ [ proc ], [ Clo (tmp, name, Zero :: value_of local env) ], Reg tmp)
  | Lam (_, abs) ->
    let f = V.blank () in
    let x, m = unbind_tm abs in
    let def, instr, v =
      trans_tm def [ (x, Reg x) ] (f :: extend_env local env) m
    in
    let name = V.freshen f in
    let tmp = V.blank () in
    let proc = { name; arg = x; body = instr; return = v } in
    (def @ [ proc ], [ Clo (tmp, name, Zero :: value_of local env) ], Reg tmp)
  | App (m, n) ->
    let def, m_instr, m_v = trans_tm def local env m in
    let def, n_instr, n_v = trans_tm def local env n in
    let tmp = V.blank () in
    (def, m_instr @ n_instr @ [ Call (tmp, m_v, n_v) ], Reg tmp)
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let def, m_instr, m_v = trans_tm def local env m in
    let def, n_instr, n_v = trans_tm def ((x, Reg x) :: local) env n in
    (def, m_instr @ [ Mov (x, m_v) ] @ n_instr, n_v)
  | Data _ -> (def, [], Zero)
  | Cons (c, ms) ->
    let def, ms_instr, ms_v =
      List.fold_left
        (fun (def, ms_instr, ms_v) m ->
          let def, m_instr, m_v = trans_tm def local env m in
          (def, ms_instr @ m_instr, ms_v @ [ m_v ]))
        (def, [], []) ms
    in
    let tmp = V.blank () in
    (def, ms_instr @ [ Struct (tmp, C.get_id c, ms_v) ], Reg tmp)
  | Case (m, cls) ->
    let def, m_instr, m_v = trans_tm def local env m in
    let tmp = V.blank () in
    let def, cls =
      List.fold_left
        (fun (def, cls) (Cl pabs) ->
          let p, rhs = unbindp_tm pabs in
          let c, p_instr, local = trans_p local p m_v in
          let def, rhs_instr, rhs_v = trans_tm def local env rhs in
          let cl =
            (C.get_id c, p_instr @ rhs_instr @ [ Mov (tmp, rhs_v); Break ])
          in
          (def, cls @ [ cl ]))
        (def, []) cls
    in
    (def, [ Switch (m_v, cls) ], Reg tmp)
  | Absurd -> (def, [], Zero)
  | Main -> (def, [], Zero)
  | _ -> failwith "TODO"

let trans_dcls dcls =
  let rec aux def local env dcls =
    match dcls with
    | [] -> (def, [], Zero)
    | DTm (x, m) :: dcls ->
      let def, m_instr, m_v = trans_tm def local env m in
      let def, instr, v = aux def ((x, Reg x) :: local) env dcls in
      (def, m_instr @ [ Mov (x, m_v) ] @ instr, v)
    | DData (_, _, _) :: dcls -> aux def local env dcls
    | _ -> failwith "TODO"
  in
  aux [] [ (Prelude.main_v, Zero) ] [] dcls
