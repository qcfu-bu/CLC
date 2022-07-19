open Fmt
open Names
open Syntax1
open Equality1
open Pprint1

let pp_map fmt map =
  let aux fmt map =
    VMap.iter (fun x m -> pf fmt "%a := %a@;<1 2>" V.pp x pp_tm m) map
  in
  pf fmt "@[<v 0>map{@;<1 2>%a}@]" aux map

module Var : sig
  type eqn = Eq of tm VMap.t * tm * tm * tm
  and eqns = eqn list

  type prbm =
    { global : eqns
    ; clause : (eqns * ps * tm_opt) list
    }

  val pp_eqn : Format.formatter -> eqn -> unit
  val pp_eqns : Format.formatter -> eqns -> unit
  val pp_prbm : Format.formatter -> prbm -> unit
  val prbm_of_cls : cls -> prbm
  val unify : eqns -> tm VMap.t
end = struct
  type eqn = Eq of tm VMap.t * tm * tm * tm
  and eqns = eqn list

  type prbm =
    { global : eqns
    ; clause : (eqns * ps * tm_opt) list
    }

  let pp_eqn fmt (Eq (_, m, n, a)) =
    pf fmt "%a ?= %a : %a" pp_tm m pp_tm n pp_tm a

  let pp_eqns fmt eqns =
    let rec aux fmt eqns =
      match eqns with
      | [] -> ()
      | [ eqn ] -> pf fmt "@[%a@]" pp_eqn eqn
      | eqn :: eqns -> pf fmt "@[%a@]@;<1 2>%a" pp_eqn eqn aux eqns
    in
    pf fmt "@[<v 0>eqns{@;<1 2>%a}@]" aux eqns

  let rec pp_clause fmt cls =
    match cls with
    | [] -> ()
    | [ (eqns, ps, rhs) ] ->
      pf fmt "[%a](%a)=>%a" pp_eqns eqns (pp_ps ", ") ps pp_tm_opt rhs
    | (eqns, ps, rhs) :: cls ->
      pf fmt "[%a](%a)=>%a@;<1 2>%a" pp_eqns eqns (pp_ps ", ") ps pp_tm_opt rhs
        pp_clause cls

  let pp_prbm fmt prbm =
    pf fmt "@[<v 0>{@;<1 2>@[global=(%a)@]@;<1 2>@[clause=(%a)@]@;<1 2>}@]"
      pp_eqns prbm.global pp_clause prbm.clause

  let rec prbm_of_cls cls : prbm =
    match cls with
    | [] -> { global = []; clause = [] }
    | Cl pabs :: cls ->
      let ps, rhs = unbindp_tm_opt pabs in
      let prbm = prbm_of_cls cls in
      { prbm with clause = ([], ps, rhs) :: prbm.clause }

  let rec occurs x m =
    match m with
    | Ann (a, m) -> occurs x a || occurs x m
    | Meta _ -> false
    | Type _ -> false
    | Var y -> V.equal x y
    | Pi (_, a, _, abs) ->
      let _, b = unbind_tm abs in
      occurs x a || occurs x b
    | Fun (a_opt, abs) ->
      let x, cls = unbind_cls abs in
      let a_res =
        match a_opt with
        | Some a -> occurs x a
        | None -> false
      in
      a_res
      || List.exists
           (fun (Cl pabs) ->
             let _, m_opt = unbindp_tm_opt pabs in
             match m_opt with
             | Some m -> occurs x m
             | None -> false)
           cls
    | App (m, n) -> occurs x m || occurs x n
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      occurs x m || occurs x n
    | Data (_, ms) -> List.exists (occurs x) ms
    | Cons (_, ms) -> List.exists (occurs x) ms
    | Absurd -> false
    | Match (ms, cls) ->
      List.exists (occurs x) ms
      || List.exists
           (fun (Cl pabs) ->
             let _, m_opt = unbindp_tm_opt pabs in
             match m_opt with
             | Some m -> occurs x m
             | None -> false)
           cls
    | If (m, tt, ff) -> occurs x m || occurs x tt || occurs x ff
    | Main -> false
    | Proto -> false
    | End -> false
    | Act (_, a, abs) ->
      let x, b = unbind_tm abs in
      occurs x a || occurs x b
    | Ch (_, a) -> occurs x a
    | Fork (a, m, abs) ->
      let x, n = unbind_tm abs in
      occurs x a || occurs x m || occurs x n
    | Send m -> occurs x m
    | Recv m -> occurs x m
    | Close m -> occurs x m

  let rec simpl (env, m1, m2) =
    if equal rd_all env m1 m2 then
      []
    else
      let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
      let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
      let _ = pr "simpl(%a, %a)@." pp_tm m1 pp_tm m2 in
      let h1, sp1 = unApps m1 in
      let h2, sp2 = unApps m2 in
      let eqns_sp =
        List.fold_left2
          (fun acc m n ->
            let eqns = simpl (env, m, n) in
            acc @ eqns)
          [] sp1 sp2
      in
      let eqns_h =
        match (h1, h2) with
        | _, Var _ -> [ (env, m1, m2) ]
        | Type s1, Type s2 ->
          if s1 = s2 then
            []
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Pi (s1, a1, _, abs1), Pi (s2, a2, _, abs2) ->
          if s1 = s2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (env, a1, a2) in
            let eqns2 = simpl (env, b1, b2) in
            eqns1 @ eqns2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
          let _, cls1, cls2 = unbind2_cls abs1 abs2 in
          let eqns1 =
            match (a1_opt, a2_opt) with
            | Some a1, Some a2 -> simpl (env, a1, a2)
            | _ -> []
          in
          let eqns2 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> simpl (env, m, n)
                | None, None -> []
                | _ -> failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2
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
        | Match (ms1, cls1), Match (ms2, cls2) ->
          let eqns1 =
            List.fold_left2 (fun acc m1 m2 -> simpl (env, m1, m2)) [] ms1 ms2
          in
          let eqns2 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> simpl (env, m, n)
                | None, None -> []
                | _ -> failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2
        | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
          let eqns1 = simpl (env, m1, m2) in
          let eqns2 = simpl (env, tt1, tt2) in
          let eqns3 = simpl (env, ff1, ff2) in
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
      if occurs x m1 then
        failwith "solve_occurs (%a, %a)" V.pp x pp_tm m1
      else
        VMap.add x m1 map
    | _ -> failwith "solve(%a, %a)" pp_tm m1 pp_tm m2

  let unify eqns =
    let eqns = List.map (fun (Eq (env, m, n, _)) -> (env, m, n)) eqns in
    let rec aux map eqns =
      let eqns =
        List.map (fun (env, m1, m2) -> (env, msubst map m1, msubst map m2)) eqns
      in
      match List.concat_map simpl eqns with
      | [] -> map
      | eqn :: eqns ->
        let map = solve map eqn in
        aux map eqns
    in
    aux VMap.empty eqns
end

module Meta : sig
  type eqn = Eq of tm VMap.t * tm * tm
  and eqns = eqn list

  type map = (tm_opt * tm_opt) MMap.t

  val pp_eqn : Format.formatter -> eqn -> unit
  val pp_eqns : Format.formatter -> eqns -> unit
  val resolve_tm : map -> tm -> tm
  val resolve_tl : map -> tl -> tl
  val resolve_ptl : map -> ptl -> ptl
  val resolve_dcons : map -> dcons -> dcons
  val resolve_dcl : map -> dcl -> dcl
  val resolve_dcls : map -> dcls -> dcls
  val unify : map -> eqns -> map
end = struct
  type eqn = Eq of tm VMap.t * tm * tm
  and eqns = eqn list

  type map = (tm_opt * tm_opt) MMap.t

  let pp_eqn fmt (Eq (_, m, n)) = pf fmt "%a ?= %a" pp_tm m pp_tm n

  let pp_eqns fmt eqns =
    let rec aux fmt eqns =
      match eqns with
      | [] -> ()
      | [ eqn ] -> pf fmt "@[%a@]" pp_eqn eqn
      | eqn :: eqns -> pf fmt "@[%a@]@;<1 2>%a" pp_eqn eqn aux eqns
    in
    pf fmt "@[<v 0>eqns{@;<1 2>%a}@]" aux eqns

  let rec fv ctx m =
    match m with
    | Ann (a, m) -> VSet.union (fv ctx a) (fv ctx m)
    | Meta (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
    | Type _ -> VSet.empty
    | Var x -> (
      match VSet.find_opt x ctx with
      | Some _ -> VSet.empty
      | None -> VSet.singleton x)
    | Pi (_, a, _, abs) ->
      let x, b = unbind_tm abs in
      let fv1 = fv ctx a in
      let fv2 = fv (VSet.add x ctx) b in
      VSet.union fv1 fv2
    | Fun (a_opt, abs) ->
      let x, cls = unbind_cls abs in
      let fv1 =
        match a_opt with
        | Some a -> fv ctx a
        | None -> VSet.empty
      in
      let fv2 =
        List.fold_left
          (fun acc (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let xs = xs_of_ps ps in
            let ctx = VSet.union (VSet.of_list (x :: xs)) ctx in
            match m_opt with
            | Some m -> VSet.union acc (fv ctx m)
            | None -> acc)
          VSet.empty cls
      in
      VSet.union fv1 fv2
    | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let fv1 = fv ctx m in
      let fv2 = fv (VSet.add x ctx) n in
      VSet.union fv1 fv2
    | Data (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
    | Cons (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
    | Match (ms, cls) ->
      let fv1 =
        List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
      in
      let fv2 =
        List.fold_left
          (fun acc (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let xs = xs_of_ps ps in
            let ctx = VSet.union (VSet.of_list xs) ctx in
            match m_opt with
            | Some m -> VSet.union acc (fv ctx m)
            | None -> acc)
          VSet.empty cls
      in
      VSet.union fv1 fv2
    | Absurd -> VSet.empty
    | If (m, tt, ff) ->
      let fv1 = fv ctx m in
      let fv2 = fv ctx tt in
      let fv3 = fv ctx ff in
      VSet.union (VSet.union fv1 fv2) fv3
    | Main -> VSet.empty
    | Proto -> VSet.empty
    | End -> VSet.empty
    | Act (_, a, abs) ->
      let x, b = unbind_tm abs in
      let fv1 = fv ctx a in
      let fv2 = fv (VSet.add x ctx) b in
      VSet.union fv1 fv2
    | Ch (_, m) -> fv ctx m
    | Fork (a, m, abs) ->
      let x, n = unbind_tm abs in
      let fv1 = fv ctx a in
      let fv2 = fv ctx m in
      let fv3 = fv (VSet.add x ctx) n in
      VSet.union (VSet.union fv1 fv2) fv3
    | Send m -> fv ctx m
    | Recv m -> fv ctx m
    | Close m -> fv ctx m

  let rec occurs x m =
    match m with
    | Ann (a, m) -> occurs x a || occurs x m
    | Meta (y, _) -> M.equal x y
    | Type _ -> false
    | Var y -> false
    | Pi (_, a, _, abs) ->
      let _, b = unbind_tm abs in
      occurs x a || occurs x b
    | Fun (a_opt, abs) ->
      let _, cls = unbind_cls abs in
      let a_res =
        match a_opt with
        | Some a -> occurs x a
        | None -> false
      in
      a_res
      || List.exists
           (fun (Cl pabs) ->
             let _, m_opt = unbindp_tm_opt pabs in
             match m_opt with
             | Some m -> occurs x m
             | None -> false)
           cls
    | App (m, n) -> occurs x m || occurs x n
    | Let (m, abs) ->
      let _, n = unbind_tm abs in
      occurs x m || occurs x n
    | Data (_, ms) -> List.exists (occurs x) ms
    | Cons (_, ms) -> List.exists (occurs x) ms
    | Absurd -> false
    | Match (ms, cls) ->
      List.exists (occurs x) ms
      || List.exists
           (fun (Cl pabs) ->
             let _, m_opt = unbindp_tm_opt pabs in
             match m_opt with
             | Some m -> occurs x m
             | None -> false)
           cls
    | If (m, tt, ff) -> occurs x m || occurs x tt || occurs x ff
    | Main -> false
    | Proto -> false
    | End -> false
    | Act (_, a, abs) ->
      let _, b = unbind_tm abs in
      occurs x a || occurs x b
    | Ch (_, a) -> occurs x a
    | Fork (a, m, abs) ->
      let _, n = unbind_tm abs in
      occurs x a || occurs x m || occurs x n
    | Send m -> occurs x m
    | Recv m -> occurs x m
    | Close m -> occurs x m

  let rec simpl (Eq (env, m1, m2)) =
    if equal rd_all env m1 m2 then
      []
    else
      let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
      let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
      let h1, sp1 = unApps m1 in
      let h2, sp2 = unApps m2 in
      let eqns_sp =
        List.fold_left2
          (fun acc m n ->
            let eqns = simpl (Eq (env, m, n)) in
            acc @ eqns)
          [] sp1 sp2
      in
      let eqns_h =
        match (h1, h2) with
        | Meta _, _ -> [ Eq (env, m1, m2) ]
        | _, Meta _ -> [ Eq (env, m2, m1) ]
        | Type s1, Type s2 ->
          if s1 = s2 then
            []
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Var x1, Var x2 ->
          if V.equal x1 x2 then
            []
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Var _, _ ->
          let m1 = whnf rd_all env m1 in
          simpl (Eq (env, m1, m2))
        | _, Var _ ->
          let m2 = whnf rd_all env m2 in
          simpl (Eq (env, m1, m2))
        | Pi (s1, a1, _, abs1), Pi (s2, a2, _, abs2) ->
          if s1 = s2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (Eq (env, a1, a2)) in
            let eqns2 = simpl (Eq (env, b1, b2)) in
            eqns1 @ eqns2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
          let _, cls1, cls2 = unbind2_cls abs1 abs2 in
          let eqns1 =
            match (a1_opt, a2_opt) with
            | Some a1, Some a2 -> simpl (Eq (env, a1, a2))
            | _ -> []
          in
          let eqns2 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> simpl (Eq (env, m, n))
                | None, None -> []
                | _ -> failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2
        | Let (m1, abs1), Let (m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (Eq (env, m1, m2)) in
          let eqns2 = simpl (Eq (env, n1, n2)) in
          eqns1 @ eqns2
        | Data (d1, ms1), Data (d2, ms2) ->
          if D.equal d1 d2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ simpl (Eq (env, m1, m2)))
              [] ms1 ms2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Cons (c1, ms1), Cons (c2, ms2) ->
          if C.equal c1 c2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ simpl (Eq (env, m1, m2)))
              [] ms1 ms2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Match (ms1, cls1), Match (ms2, cls2) ->
          let eqns1 =
            List.fold_left2
              (fun acc m1 m2 -> simpl (Eq (env, m1, m2)))
              [] ms1 ms2
          in
          let eqns2 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> simpl (Eq (env, m, n))
                | None, None -> []
                | _ -> failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2
        | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
          let eqns1 = simpl (Eq (env, m1, m2)) in
          let eqns2 = simpl (Eq (env, tt1, tt2)) in
          let eqns3 = simpl (Eq (env, ff1, ff2)) in
          eqns1 @ eqns2 @ eqns3
        | Main, Main -> []
        | Proto, Proto -> []
        | End, End -> []
        | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
          if r1 = r2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (Eq (env, a1, a2)) in
            let eqns2 = simpl (Eq (env, b1, b2)) in
            eqns1 @ eqns2
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Ch (r1, a1), Ch (r2, a2) ->
          if r1 = r2 then
            simpl (Eq (env, a1, a2))
          else
            failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (Eq (env, a1, a2)) in
          let eqns2 = simpl (Eq (env, m1, m2)) in
          let eqns3 = simpl (Eq (env, n1, n2)) in
          eqns1 @ eqns2 @ eqns3
        | Send m1, Send m2 -> simpl (Eq (env, m1, m2))
        | Recv m1, Recv m2 -> simpl (Eq (env, m1, m2))
        | Close m1, Close m2 -> simpl (Eq (env, m1, m2))
        | _ -> failwith "simpl(%a, %a)" pp_tm m1 pp_tm m2
      in
      eqns_h @ eqns_sp

  let meta_spine sp =
    List.map
      (fun m ->
        match m with
        | Var x -> x
        | _ -> V.mk "")
      sp

  let solve map (Eq (env, m1, m2)) =
    let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
    let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
    match (m1, m2) with
    | Meta (x, xs), _ ->
      if occurs x m2 then
        failwith "occurs(%a, %a)" M.pp x pp_tm m2
      else
        let xs = meta_spine xs in
        let ctx = fv VSet.empty m2 in
        if VSet.subset ctx (VSet.of_list xs) then
          let ps = List.map (fun x -> PVar x) xs in
          let cls = Cl (bindp_tm_opt ps (Some m2)) in
          let m = Fun (None, bind_cls V.blank [ cls ]) in
          MMap.add x (Some m, None) map
        else
          failwith "solve(%a, %a)" pp_tm m1 pp_tm m2
    | _ -> failwith "solve(%a, %a)" pp_tm m1 pp_tm m2

  let rec resolve_tm map m =
    match m with
    | Meta (x, xs) -> (
      try
        match MMap.find x map with
        | Some h, _ ->
          let m = mkApps h xs in
          resolve_tm map (whnf [ Beta; Iota; Zeta ] VMap.empty m)
        | _ -> m
      with
      | _ -> m)
    | Ann (a, m) -> Ann (resolve_tm map a, resolve_tm map m)
    | Type _ -> m
    | Var _ -> m
    | Pi (s, a, impl, abs) ->
      let x, b = unbind_tm abs in
      let a = resolve_tm map a in
      let b = resolve_tm map b in
      Pi (s, a, impl, bind_tm x b)
    | Fun (a_opt, abs) ->
      let x, cls = unbind_cls abs in
      let a_opt = Option.map (resolve_tm map) a_opt in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (resolve_tm map) m_opt in
            Cl (bindp_tm_opt ps m_opt))
          cls
      in
      Fun (a_opt, bind_cls x cls)
    | App (m, n) ->
      let m = resolve_tm map m in
      let n = resolve_tm map n in
      App (m, n)
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let m = resolve_tm map m in
      let n = resolve_tm map n in
      Let (m, bind_tm x n)
    | Data (d, ms) ->
      let ms = List.map (resolve_tm map) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (resolve_tm map) ms in
      Cons (c, ms)
    | Absurd -> Absurd
    | Match (ms, cls) ->
      let ms = List.map (resolve_tm map) ms in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (resolve_tm map) m_opt in
            Cl (bindp_tm_opt ps m_opt))
          cls
      in
      Match (ms, cls)
    | If (m, tt, ff) ->
      let m = resolve_tm map m in
      let tt = resolve_tm map tt in
      let ff = resolve_tm map ff in
      If (m, tt, ff)
    | Main -> m
    | Proto -> m
    | End -> m
    | Act (r, a, abs) ->
      let x, b = unbind_tm abs in
      let a = resolve_tm map a in
      let b = resolve_tm map b in
      Act (r, a, bind_tm x b)
    | Ch (r, m) -> Ch (r, resolve_tm map m)
    | Fork (a, m, abs) ->
      let x, n = unbind_tm abs in
      let a = resolve_tm map a in
      let m = resolve_tm map m in
      let n = resolve_tm map n in
      Fork (a, m, bind_tm x n)
    | Send m -> Send (resolve_tm map m)
    | Recv m -> Recv (resolve_tm map m)
    | Close m -> Close (resolve_tm map m)

  let rec resolve_tl map tl =
    match tl with
    | TBase b -> TBase (resolve_tm map b)
    | TBind (a, impl, abs) ->
      let x, tl = unbind_tl abs in
      let a = resolve_tm map a in
      let tl = resolve_tl map tl in
      TBind (a, impl, bind_tl x tl)

  let rec resolve_ptl map ptl =
    match ptl with
    | PBase tl -> PBase (resolve_tl map tl)
    | PBind (a, impl, abs) ->
      let x, ptl = unbind_ptl abs in
      let a = resolve_tm map a in
      let ptl = resolve_ptl map ptl in
      PBind (a, impl, bind_ptl x ptl)

  let rec resolve_dcons map (DCons (c, ptl)) = DCons (c, resolve_ptl map ptl)

  let resolve_dcl map dcl =
    match dcl with
    | DTm (x, a_opt, m) ->
      let a_opt = Option.map (resolve_tm map) a_opt in
      let m = resolve_tm map m in
      DTm (x, a_opt, m)
    | DFun (x, a, abs) ->
      let y, cls = unbind_cls abs in
      let a = resolve_tm map a in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (resolve_tm map) m_opt in
            Cl (bindp_tm_opt ps m_opt))
          cls
      in
      DFun (x, a, bind_cls y cls)
    | DData (d, ptl, dconss) ->
      let ptl = resolve_ptl map ptl in
      let dconss = List.map (resolve_dcons map) dconss in
      DData (d, ptl, dconss)
    | DOpen _ -> dcl
    | DAxiom (x, a) -> DAxiom (x, resolve_tm map a)

  let resolve_dcls map dcls = List.map (resolve_dcl map) dcls

  let rec unify map eqns =
    let eqns =
      List.map
        (fun (Eq (env, m1, m2)) ->
          Eq (env, resolve_tm map m1, resolve_tm map m2))
        eqns
    in
    match List.concat_map simpl eqns with
    | [] -> map
    | eqn :: eqns ->
      let map = solve map eqn in
      unify map eqns
end