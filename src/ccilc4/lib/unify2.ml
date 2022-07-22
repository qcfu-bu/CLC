open Fmt
open Names
open Syntax2
open Equality2
open Pprint2

let pp_map fmt map =
  let aux fmt map =
    VMap.iter (fun x m -> pf fmt "%a := %a@;<1 2>" V.pp x pp_tm m) map
  in
  pf fmt "@[<v 0>map{@;<1 2>%a}@]" aux map

module UVar = struct
  type eqn = Eq of tm VMap.t * tm * Syntax1.p * tm
  and eqns = eqn list

  type prbm =
    { global : eqns
    ; clause : (eqns * Syntax1.ps * Syntax1.tm_opt) list
    }

  let pp_eqn fmt (Eq (_, m, n, a)) =
    pf fmt "(%a ?= %a : %a)" pp_tm m Pprint1.pp_p n pp_tm a

  let pp_eqns fmt eqns =
    let rec aux fmt eqns =
      match eqns with
      | [] -> ()
      | [ eqn ] -> pf fmt "@[%a@]" pp_eqn eqn
      | eqn :: eqns -> pf fmt "@[%a@]@;<1 0>%a" pp_eqn eqn aux eqns
    in
    pf fmt "@[eqns{@;<1 2>%a}@]" aux eqns

  let rec pp_clause fmt cls =
    match cls with
    | [] -> ()
    | [ (eqns, ps, rhs) ] ->
      pf fmt "[%a](%a)=>@;<1 2>%a" pp_eqns eqns (Pprint1.pp_ps ", ") ps
        (option Syntax1.pp_tm) rhs
    | (eqns, ps, rhs) :: cls ->
      pf fmt "[%a](%a)=>@;<1 2>%a@;<1 0>%a" pp_eqns eqns (Pprint1.pp_ps ", ") ps
        (option Syntax1.pp_tm) rhs pp_clause cls

  let pp_prbm fmt prbm =
    pf fmt
      "@[{@;\
       <1 2>@[global=(@;\
       <1 2>@[%a@])@]@;\
       <1 2>@[clause=(@;\
       <1 2>@[<v 0>%a@])@]@;\
       <1 0>}@]" pp_eqns prbm.global pp_clause prbm.clause

  let rec prbm_of_cls cls : prbm =
    match cls with
    | [] -> { global = []; clause = [] }
    | Syntax1.Cl pabs :: cls ->
      let ps, rhs = Syntax1.unbindp_tm_opt pabs in
      let prbm = prbm_of_cls cls in
      { prbm with clause = ([], ps, rhs) :: prbm.clause }

  let rec simpl (env, m1, m2) =
    if equal rd_all env m1 m2 then
      []
    else
      let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
      let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
      let h1, sp1 = unApps m1 in
      let h2, sp2 = unApps m2 in
      let eqns_sp =
        try
          List.fold_left2
            (fun acc m n ->
              let eqns = simpl (env, m, n) in
              acc @ eqns)
            [] sp1 sp2
        with
        | _ -> failwith "simpl(%a ?=@;<1 2> %a)" pp_tm m1 pp_tm m2
      in
      let eqns_h =
        match (h1, h2) with
        | _, Var _ -> [ (env, m1, m2) ]
        | Var _, _ -> [ (env, m2, m1) ]
        | Type s1, Type s2 ->
          if s1 = s2 then
            []
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Pi (s1, a1, abs1), Pi (s2, a2, abs2) ->
          if s1 = s2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (env, a1, a2) in
            let eqns2 = simpl (env, b1, b2) in
            eqns1 @ eqns2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fix (a1, abs1), Fix (a2, abs2) ->
          let _, m1, m2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, a1, a2) in
          let eqns2 = simpl (env, m1, m2) in
          eqns1 @ eqns2
        | Lam (s1, abs1), Lam (s2, abs2) ->
          if s1 = s2 then
            let _, m1, m2 = unbind2_tm abs1 abs2 in
            simpl (env, m1, m2)
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Let (m1, abs1), Let (m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, m1, m2) in
          let eqns2 = simpl (env, n1, n2) in
          eqns1 @ eqns2
        | Data (d1, ms1), Data (d2, ms2) ->
          if D.equal d1 d2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
              [] ms1 ms2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Cons (c1, ms1), Cons (c2, ms2) ->
          if C.equal c1 c2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
              [] ms1 ms2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Case (m1, a1, cls1), Case (m2, a2, cls2) ->
          let eqns1 = simpl (env, m1, m2) in
          let eqns2 = simpl (env, a1, a2) in
          let eqns3 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m, n = unbindp2_tm pabs1 pabs2 in
                simpl (env, m, n))
              [] cls1 cls2
          in
          eqns1 @ eqns2 @ eqns3
        | Main, Main -> []
        | Proto, Proto -> []
        | End, End -> []
        | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
          if r1 = r2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (env, a1, a2) in
            let eqns2 = simpl (env, b1, b2) in
            eqns1 @ eqns2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Ch (r1, a1), Ch (r2, a2) ->
          if r1 = r2 then
            simpl (env, a1, a2)
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, a1, a2) in
          let eqns2 = simpl (env, m1, m2) in
          let eqns3 = simpl (env, n1, n2) in
          eqns1 @ eqns2 @ eqns3
        | Send m1, Send m2 -> simpl (env, m1, m2)
        | Recv m1, Recv m2 -> simpl (env, m1, m2)
        | Close m1, Close m2 -> simpl (env, m1, m2)
        | _ -> failwith "simpl(%a, %a)" pp_tm m1 pp_tm m2
      in
      eqns_h @ eqns_sp

  let solve map (env, m1, m2) =
    let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
    let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
    match (m1, m2) with
    | _, Var x ->
      if occurs_tm x m1 then
        failwith "solve_occurs (%a, %a)" V.pp x pp_tm m1
      else
        VMap.add x m1 map
    | _ -> failwith "solve(%a, %a)" pp_tm m1 pp_tm m2

  let rec msubst_tm map m =
    match m with
    | Ann (a, m) ->
      let a = msubst_tm map a in
      let m = msubst_tm map m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (msubst_tm map) ms in
      Meta (x, ms)
    | Type s -> Type s
    | Var x -> (
      match VMap.find_opt x map with
      | Some m -> m
      | None -> Var x)
    | Pi (s, a, abs) ->
      let a = msubst_tm map a in
      let x, b = unbind_tm abs in
      let b = msubst_tm map b in
      Pi (s, a, bind_tm x b)
    | Fix (a, abs) ->
      let a = msubst_tm map a in
      let x, m = unbind_tm abs in
      let m = msubst_tm map m in
      Fix (a, bind_tm x m)
    | Lam (s, abs) ->
      let x, m = unbind_tm abs in
      let m = msubst_tm map m in
      Lam (s, bind_tm x m)
    | App (m, n) ->
      let m = msubst_tm map m in
      let n = msubst_tm map n in
      App (m, n)
    | Let (m, abs) ->
      let m = msubst_tm map m in
      let x, n = unbind_tm abs in
      let n = msubst_tm map n in
      Let (m, bind_tm x n)
    | Data (d, ms) ->
      let ms = List.map (msubst_tm map) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (msubst_tm map) ms in
      Cons (c, ms)
    | Case (m, a, cls) ->
      let m = msubst_tm map m in
      let a = msubst_tm map a in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let p, rhs = unbindp_tm pabs in
            let rhs = msubst_tm map rhs in
            Cl (bindp_tm p rhs))
          cls
      in
      Case (m, a, cls)
    | Main -> Main
    | Proto -> Proto
    | End -> End
    | Act (r, a, abs) ->
      let a = msubst_tm map a in
      let x, b = unbind_tm abs in
      let b = msubst_tm map b in
      Act (r, a, bind_tm x b)
    | Ch (r, a) ->
      let a = msubst_tm map a in
      Ch (r, a)
    | Fork (a, m, abs) ->
      let a = msubst_tm map a in
      let m = msubst_tm map m in
      let x, n = unbind_tm abs in
      let n = msubst_tm map n in
      Fork (a, m, bind_tm x n)
    | Send m ->
      let m = msubst_tm map m in
      Send m
    | Recv m ->
      let m = msubst_tm map m in
      Recv m
    | Close m ->
      let m = msubst_tm map m in
      Close m

  let rec tm_of_p p =
    match p with
    | Syntax1.PVar x -> Var x
    | Syntax1.PCons (c, ps) -> Cons (c, List.map tm_of_p ps)
    | Syntax1.PAbsurd -> failwith "tm_of_p"

  let unify eqns =
    let eqns = List.map (fun (Eq (env, m, p, _)) -> (env, m, tm_of_p p)) eqns in
    let rec aux map eqns =
      let eqns =
        List.map
          (fun (env, m1, m2) -> (env, msubst_tm map m1, msubst_tm map m2))
          eqns
      in
      match List.concat_map simpl eqns with
      | [] -> map
      | eqn :: eqns ->
        let map = solve map eqn in
        aux map eqns
    in
    aux VMap.empty eqns
end