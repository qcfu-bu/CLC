open Format
open Bindlib
open Name
open Context
open Core
open Tm
open Pprint

let failwith s =
  let _ = printf "%s\n" s in
  failwith "unify"

let union m1 m2 =
  MMap.union
    (fun _ (x, opt1, ord1) (y, opt2, ord2) ->
      let opt =
        match (opt1, opt2) with
        | Some a, Some _ -> Some a
        | Some _, None -> opt1
        | None, Some _ -> opt2
        | _, _ -> None
      in
      if ord1 < ord2 then
        Some (y, opt, ord2)
      else
        Some (x, opt, ord1))
    m1 m2

let rec fv ctx t =
  match t with
  | Ann (m, a) -> VSet.union (fv ctx m) (fv ctx a)
  | Meta _ -> VSet.empty
  | Knd _ -> VSet.empty
  | Var x -> (
    match VSet.find_opt x ctx with
    | Some _ -> VSet.empty
    | None -> VSet.singleton x)
  | Pi (_, a, b) ->
    let x, ub = unbind b in
    let fv1 = fv ctx a in
    let fv2 = fv (VSet.add x ctx) ub in
    VSet.union fv1 fv2
  | Lam (_, m) ->
    let x, um = unbind m in
    fv (VSet.add x ctx) um
  | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
  | Let (m, n) ->
    let x, un = unbind n in
    let fv1 = fv ctx m in
    let fv2 = fv (VSet.add x ctx) un in
    VSet.union fv1 fv2
  | Ind (_, ms) ->
    let fvs = List.map (fv ctx) ms in
    List.fold_left VSet.union VSet.empty fvs
  | Constr (_, ms) ->
    let fvs = List.map (fv ctx) ms in
    List.fold_left VSet.union VSet.empty fvs
  | Match (m, mot, cls) -> (
    let fv1 = fv ctx m in
    let fv2 =
      List.fold_left
        (fun acc cl ->
          let p, ucl = unbind_p cl in
          let xs = list_of_p p in
          let ctx = VSet.union ctx (VSet.of_list xs) in
          VSet.union acc (fv ctx ucl))
        VSet.empty cls
    in
    let res = VSet.union fv1 fv2 in
    match mot with
    | Mot0 -> res
    | Mot1 mot ->
      let x, umot = unbind mot in
      let ctx = VSet.add x ctx in
      let fv3 = fv ctx umot in
      VSet.union res fv3
    | Mot2 mot ->
      let p, umot = unbind_p mot in
      let xs = list_of_p p in
      let ctx = VSet.union ctx (VSet.of_list xs) in
      let fv3 = fv ctx umot in
      VSet.union res fv3
    | Mot3 mot ->
      let x, mot = unbind mot in
      let p, umot = unbind_p mot in
      let xs = list_of_p p in
      let ctx = VSet.add x ctx in
      let ctx = VSet.union ctx (VSet.of_list xs) in
      let fv3 = fv ctx umot in
      VSet.union res fv3)
  | Fix m ->
    let x, um = unbind m in
    fv (VSet.add x ctx) um
  | Axiom (_, m) -> fv ctx m

let rec occurs x m =
  match m with
  | Ann (m, a) -> occurs x m || occurs x a
  | Meta y -> Meta.equal x y
  | Knd _ -> false
  | Var _ -> false
  | Pi (_, a, b) ->
    let _, ub = unbind b in
    occurs x a || occurs x ub
  | Lam (_, m) ->
    let _, um = unbind m in
    occurs x um
  | App (m, n) -> occurs x m || occurs x n
  | Let (m, n) ->
    let _, un = unbind n in
    occurs x m || occurs x un
  | Ind (_, ms) -> List.exists (fun m -> occurs x m) ms
  | Constr (_, ms) -> List.exists (fun m -> occurs x m) ms
  | Match (m, mot, cls) -> (
    let ucls = List.map (fun cl -> snd (unbind_p cl)) cls in
    if occurs x m || List.exists (fun ucl -> occurs x ucl) ucls then
      true
    else
      match mot with
      | Mot0 -> false
      | Mot1 mot ->
        let _, umot = unbind mot in
        occurs x umot
      | Mot2 mot ->
        let _, umot = unbind_p mot in
        occurs x umot
      | Mot3 mot ->
        let _, mot = unbind mot in
        let _, umot = unbind_p mot in
        occurs x umot)
  | Fix m ->
    let _, um = unbind m in
    occurs x um
  | Axiom (_, m) -> occurs x m

let rec simpl env eqn =
  let m1, m2 = eqn in
  if equal env m1 m2 then
    []
  else
    let m1 = whnf m1 in
    let m2 = whnf m2 in
    let h1, sp1 = spine m1 in
    let h2, sp2 = spine m2 in
    match (h1, h2) with
    | Var x1, Var x2 ->
      if eq_vars x1 x2 then
        List.fold_left2 (fun acc m1 m2 -> acc @ simpl env (m1, m2)) [] sp1 sp2
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | Meta _, _ -> [ eqn ]
    | _, Meta _ -> [ (m2, m1) ]
    | Knd s1, Knd s2 ->
      if s1 = s2 then
        []
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | Var _, _ ->
      let m1 = zdnf env m1 in
      simpl env (m1, m2)
    | _, Var _ ->
      let m2 = zdnf env m2 in
      simpl env (m1, m2)
    | Pi (s1, a1, b1), Pi (s2, a2, b2) ->
      if s1 = s2 then
        let _, ub1, ub2 = unbind2 b1 b2 in
        let eqn1 = simpl env (a1, a2) in
        let eqn2 = simpl env (ub1, ub2) in
        eqn1 @ eqn2
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | Lam (s1, m1), Lam (s2, m2) ->
      if s1 = s2 then
        let _, um1, um2 = unbind2 m1 m2 in
        simpl env (um1, um2)
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | Let (m1, n1), Let (m2, n2) ->
      let _, un1, un2 = unbind2 n1 n2 in
      let eqn1 = simpl env (m1, m2) in
      let eqn2 = simpl env (un1, un2) in
      eqn1 @ eqn2
    | Ind (id1, ms1), Ind (id2, ms2) ->
      if Id.equal id1 id2 then
        List.fold_left2 (fun acc m1 m2 -> acc @ simpl env (m1, m2)) [] ms1 ms2
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | Constr (id1, ms1), Constr (id2, ms2) ->
      if Id.equal id1 id2 then
        List.fold_left2 (fun acc m1 m2 -> acc @ simpl env (m1, m2)) [] ms1 ms2
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
      let eqn1 = simpl env (m1, m2) in
      let eqn2 =
        match (mot1, mot2) with
        | Mot0, Mot0 -> []
        | Mot1 mot1, Mot1 mot2 ->
          let _, umot1, umot2 = unbind2 mot1 mot2 in
          simpl env (umot1, umot2)
        | Mot2 mot1, Mot2 mot2 ->
          let _, umot1, umot2 = unbind_p2 mot1 mot2 in
          simpl env (umot1, umot2)
        | Mot3 mot1, Mot3 mot2 ->
          let _, mot1, mot2 = unbind2 mot1 mot2 in
          let _, umot1, umot2 = unbind_p2 mot1 mot2 in
          simpl env (umot1, umot2)
        | _ -> failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
      in
      let eqn3 =
        List.fold_left2
          (fun acc cl1 cl2 ->
            let _, ucl1, ucl2 = unbind_p2 cl1 cl2 in
            acc @ simpl env (ucl1, ucl2))
          [] cls1 cls2
      in
      eqn1 @ eqn2 @ eqn3
    | Fix m1, Fix m2 ->
      let _, um1, um2 = unbind2 m1 m2 in
      simpl env (um1, um2)
    | Axiom (id1, m1), Axiom (id2, m2) ->
      if Id.equal id1 id2 then
        let eqn1 = simpl env (m1, m2) in
        let eqn2 =
          List.fold_left2 (fun acc m1 m2 -> acc @ simpl env (m1, m2)) [] sp1 sp2
        in
        eqn1 @ eqn2
      else
        failwith (asprintf "simpl failure(%a, %a)" Tm.pp h1 Tm.pp h2)
    | _ -> failwith (asprintf "xsimpl failure(%a, %a)" Tm.pp m1 Tm.pp m2)

let solve eqn =
  let strip sp =
    List.map
      (fun m ->
        match m with
        | Var x -> x
        | _ -> mk "")
      sp
  in
  let m1, m2 = eqn in
  let m1 = whnf m1 in
  let m2 = whnf m2 in
  let h1, sp1 = spine m1 in
  let h2, sp2 = spine m2 in
  match (h1, h2) with
  | Meta x1, Meta x2 ->
    let xs = strip sp1 in
    let ys = strip sp2 in
    let ctx = VSet.inter (VSet.of_list xs) (VSet.of_list ys) in
    let zs = List.map _Var (VSet.elements ctx) in
    let xs =
      List.map
        (fun x ->
          match VSet.find_opt x ctx with
          | Some _ -> x
          | None -> mk "")
        xs
    in
    let ys =
      List.map
        (fun y ->
          match VSet.find_opt y ctx with
          | Some _ -> y
          | None -> mk "")
        ys
    in
    let m = _Meta (Meta.mk ()) in
    let m = _mApp m zs in
    let m1 = unbox (_mLam U xs m) in
    let m2 = unbox (_mLam U ys m) in
    let res = MMap.empty in
    let res = MMap.add x1 (Some m1, None, 0) res in
    let res = MMap.add x2 (Some m2, None, 0) res in
    res
  | Meta x, _ ->
    if occurs x m2 then
      failwith (asprintf "meta(%a) occurs in term(%a)" Meta.pp x Tm.pp m2)
    else
      let xs = strip sp1 in
      let ctx = fv VSet.empty m2 in
      if VSet.subset ctx (VSet.of_list xs) then
        let m = unbox (_mLam U xs (lift m2)) in
        MMap.singleton x (Some m, None, 1)
      else
        failwith (asprintf "solve failure(%a, %a)" Tm.pp m1 Tm.pp m2)
  | _ -> failwith (asprintf "solve failure(%a, %a)" Tm.pp m1 Tm.pp m2)

module UnifyTm = struct
  let rec resolve mmap m =
    let h, sp = spine m in
    match h with
    | Meta x -> (
      try
        match MMap.find x mmap with
        | Some h, _, _ ->
          let sp = List.map lift sp in
          let t = unbox (_mApp (lift h) sp) in
          resolve mmap (whnf t)
        | _ -> m
      with
      | _ -> m)
    | _ -> (
      match m with
      | Ann (m, a) -> Ann (resolve mmap m, resolve mmap a)
      | Knd _ -> m
      | Var _ -> m
      | Pi (s, a, b) ->
        let x, ub = unbind b in
        let a = resolve mmap a in
        let ub = resolve mmap ub in
        let b = unbox (bind_var x (lift ub)) in
        Pi (s, a, b)
      | Lam (s, m) ->
        let x, um = unbind m in
        let um = resolve mmap um in
        let m = unbox (bind_var x (lift um)) in
        Lam (s, m)
      | App (m, n) ->
        let m = resolve mmap m in
        let n = resolve mmap n in
        App (m, n)
      | Let (m, n) ->
        let x, un = unbind n in
        let m = resolve mmap m in
        let un = resolve mmap un in
        let n = unbox (bind_var x (lift un)) in
        Let (m, n)
      | Ind (id, ms) ->
        let ms = List.map (resolve mmap) ms in
        Ind (id, ms)
      | Constr (id, ms) ->
        let ms = List.map (resolve mmap) ms in
        Constr (id, ms)
      | Match (m, mot, cls) ->
        let m = resolve mmap m in
        let mot =
          match mot with
          | Mot0 -> Mot0
          | Mot1 mot ->
            let x, umot = unbind mot in
            let umot = resolve mmap umot in
            let mot = bind_var x (lift umot) in
            Mot1 (unbox mot)
          | Mot2 mot ->
            let p, umot = unbind_p mot in
            let umot = resolve mmap umot in
            let mot = bind_p p (lift umot) in
            Mot2 (unbox mot)
          | Mot3 mot ->
            let x, mot = unbind mot in
            let p, umot = unbind_p mot in
            let umot = resolve mmap umot in
            let mot = bind_var x (bind_p p (lift umot)) in
            Mot3 (unbox mot)
        in
        let cls =
          List.map
            (fun cl ->
              let p, ucl = unbind_p cl in
              let ucl = resolve mmap ucl in
              unbox (bind_p p (lift ucl)))
            cls
        in
        Match (m, mot, cls)
      | Fix m ->
        let x, um = unbind m in
        let um = resolve mmap um in
        let m = unbox (bind_var x (lift um)) in
        Fix m
      | Axiom (id, m) -> Axiom (id, resolve mmap m)
      | _ -> failwith (asprintf "resolve failure(%a)" Tm.pp m))
end

module UnifyTp = struct
  open Tm
  open Tp
  open UnifyTm

  let rec resolve mmap tp =
    match tp with
    | Main m ->
      let m = UnifyTm.resolve mmap m in
      _Main (lift m)
    | Define (m, tp) ->
      let x, utp = unbind tp in
      let m = UnifyTm.resolve mmap m in
      let utp = resolve mmap utp in
      let tp = bind_var x utp in
      _Define (lift m) tp
    | Induct (ind, tp) ->
      let ind = resolve_ind mmap ind in
      let tp = resolve mmap tp in
      _Induct ind tp

  and resolve_ind mmap (Ind (id, a, cs)) =
    let a = resolve_pscope mmap a in
    let cs = List.map (resolve_constr mmap) cs in
    let cs = box_list cs in
    _Ind id a cs

  and resolve_constr mmap (Constr (id, a)) =
    let a = resolve_pscope mmap a in
    _Constr id a

  and resolve_pscope mmap a =
    match a with
    | PBase a -> _PBase (resolve_tscope mmap a)
    | PBind (a, b) ->
      let x, ub = unbind b in
      let a = UnifyTm.resolve mmap a in
      let ub = resolve_pscope mmap ub in
      let b = bind_var x ub in
      _PBind (lift a) b

  and resolve_tscope mmap a =
    match a with
    | TBase a ->
      let a = UnifyTm.resolve mmap a in
      _TBase (lift a)
    | TBind (a, b) ->
      let x, ub = unbind b in
      let a = UnifyTm.resolve mmap a in
      let ub = resolve_tscope mmap ub in
      let b = bind_var x ub in
      _TBind (lift a) b
end

let rec unify env mmap eqns =
  match List.concat_map (simpl env) eqns with
  | [] -> mmap
  | eqns ->
    let mmaps = List.map solve eqns in
    let mmap = List.fold_left (fun acc mmap -> union acc mmap) mmap mmaps in
    let eqns =
      List.map
        (fun (m1, m2) -> (UnifyTm.resolve mmap m1, UnifyTm.resolve mmap m2))
        eqns
    in
    unify env mmap eqns
