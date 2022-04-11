open Format
open Bindlib
open Name
open Core
open Prelude

module Context = struct
  open Term
  open Top
  module IMap = Map.Make (Id)

  let find_v x ctx =
    try VMap.find x ctx with
    | _ -> failwith (asprintf "unbound variable(%a)" pp_v x)

  let find_id id ctx =
    try IMap.find id ctx with
    | _ -> failwith (asprintf "unbound identifier(%a)" Id.pp id)

  let find_idc id ctx =
    let opt =
      IMap.fold
        (fun _ (Ind (_, _, cs)) acc ->
          match acc with
          | Some _ -> acc
          | None ->
            List.fold_left
              (fun acc (Constr (idc, ps)) ->
                match acc with
                | Some _ -> acc
                | None ->
                  if Id.equal id idc then
                    Some (Constr (idc, ps))
                  else
                    None)
              None cs)
        ctx None
    in
    match opt with
    | Some c -> c
    | None -> failwith (asprintf "unbound identifier(%a)" Id.pp id)

  let equal ctx1 ctx2 = VMap.equal (fun _ _ -> true) ctx1 ctx2

  let remove x ctx s =
    match s with
    | U -> ctx
    | L ->
      if VMap.exists (fun y _ -> eq_vars x y) ctx then
        ctx
      else
        failwith (asprintf "unused variable(%a)" pp_v x)

  let merge ctx1 ctx2 =
    VMap.merge
      (fun _ x1 x2 ->
        match (x1, x2) with
        | Some _, Some _ -> failwith "merge duplication"
        | Some _, None -> x1
        | None, Some _ -> x2
        | None, None -> None)
      ctx1 ctx2
end

module CheckTerm = struct
  open Term
  open Context

  let rec dual m =
    let m = whnf m in
    match m with
    | Inp (a, b) ->
      let x, ub = unbind b in
      let ub = dual ub in
      let b = unbox (bind_var x (lift ub)) in
      Out (a, b)
    | Out (a, b) ->
      let x, ub = unbind b in
      let ub = dual ub in
      let b = unbox (bind_var x (lift ub)) in
      Inp (a, b)
    | Match (m, mot, cls) ->
      let cls =
        List.map
          (fun cl ->
            let p, ucl = unbind_p cl in
            let ucl = dual ucl in
            unbox (bind_p p (lift ucl)))
          cls
      in
      Match (m, mot, cls)
    | _ -> failwith (asprintf "dual error(%a)" Term.pp m)

  let rec infer_sort vctx ictx m =
    let a, ctx = infer vctx ictx m in
    match whnf a with
    | Knd s ->
      if VMap.is_empty ctx then
        s
      else
        failwith "impure context"
    | _ -> failwith "unexpected type"

  and infer vctx ictx m =
    match m with
    | Ann (m, a) -> (
      let _ = infer_sort vctx ictx a in
      match m with
      | Let (m, n) ->
        let x, un = unbind n in
        let n = unbox (bind_var x (lift (Ann (un, a)))) in
        let ctx = check vctx ictx (Let (m, n)) a in
        (a, ctx)
      | _ ->
        let ctx = check vctx ictx m a in
        (a, ctx))
    | Meta x -> failwith (asprintf "infer meta(%a)" Meta.pp x)
    | Knd _ -> (Knd U, VMap.empty)
    | Var x -> (
      let a, s = find_v x vctx in
      match s with
      | U -> (a, VMap.empty)
      | L -> (a, VMap.singleton x a))
    | Pi (s, a, b) ->
      let x, ub = unbind b in
      let t = infer_sort vctx ictx a in
      let _ = infer_sort (VMap.add x (a, t) vctx) ictx ub in
      (Knd s, VMap.empty)
    | Lam _ -> failwith (asprintf "infer lam(%a)" Term.pp m)
    | App (m, n) -> (
      let a, ctx1 = infer vctx ictx m in
      match whnf a with
      | Pi (s, a, b) -> (
        let t = infer_sort vctx ictx a in
        let ctx2 = check vctx ictx n a in
        match t with
        | U ->
          if VMap.is_empty ctx2 then
            (subst b n, merge ctx1 ctx2)
          else
            failwith (asprintf "impure arg(%a)" Term.pp n)
        | L -> (subst b n, merge ctx1 ctx2))
      | _ -> failwith (asprintf "infer app(%a)" Term.pp m))
    | Let (m, n) ->
      let a, ctx1 = infer vctx ictx m in
      let s = infer_sort vctx ictx a in
      let b, ctx2 =
        match s with
        | U when VMap.is_empty ctx1 -> infer vctx ictx (subst n m)
        | U -> failwith (asprintf "import let(%a)" Term.pp m)
        | L ->
          let x, un = unbind n in
          let b, ctx2 = infer (VMap.add x (a, s) vctx) ictx un in
          (b, remove x ctx2 s)
      in
      (b, merge ctx1 ctx2)
    | Ind (id, ms) ->
      let (Top.Ind (_, a, _)) = find_id id ictx in
      infer_pscope vctx ictx ms a
    | Constr (id, ms) ->
      let (Top.Constr (_, a)) = find_idc id ictx in
      infer_pscope vctx ictx ms a
    | Match (m, mot, cls) -> (
      let a, ctx1 = infer vctx ictx m in
      let s = infer_sort vctx ictx a in
      let a = whnf a in
      match a with
      | Ind (id, ms) -> (
        let (Top.Ind (_, _, cs)) = find_id id ictx in
        let cover = coverage vctx ictx cls cs ms in
        match (s, mot) with
        | _, Mot0 -> (
          let ctxs = infer_cover cover ictx in
          match ctxs with
          | [] -> failwith "infer motive error"
          | (a, ctx2) :: ctxs ->
            List.fold_left
              (fun acc (a', ctx) ->
                if equal a a' && Context.equal ctx ctx2 then
                  acc
                else
                  failwith "mot0 error")
              (a, Context.merge ctx1 ctx2)
              ctxs)
        | U, Mot1 mot -> (
          let a = subst mot m in
          let ctxs = check_motive cover ictx mot s in
          match ctxs with
          | [] -> (a, ctx1)
          | ctx2 :: ctxs ->
            if VMap.is_empty ctx1 then
              List.fold_left
                (fun acc ctx ->
                  if Context.equal ctx1 ctx2 then
                    acc
                  else
                    failwith "mot1 error")
                (a, merge ctx1 ctx2)
                ctxs
            else
              failwith "mot1 impure context")
        | _, Mot2 mot -> (
          let a = subst_p mot a in
          let ctxs = check_motive cover ictx mot s in
          match ctxs with
          | [] -> (a, ctx1)
          | ctx2 :: ctxs ->
            List.fold_left
              (fun acc ctx ->
                if Context.equal ctx1 ctx2 then
                  acc
                else
                  failwith "mot2 error")
              (a, merge ctx1 ctx2)
              ctxs)
        | U, Mot3 mot -> (
          let a = subst_p (subst mot m) a in
          let ctxs = check_motive ictx mot s in
          match ctxs with
          | [] -> (a, ctx1)
          | ctx2 :: ctxs ->
            if VMap.is_empty ctx1 then
              List.fold_left
                (fun acc ctx ->
                  if Context.equal ctx1 ctx2 then
                    acc
                  else
                    failwith "mot3 error")
                (a, merge ctx1 ctx2)
                ctxs
            else
              failwith "mot3 impure context")
        | _ -> failwith (asprintf "linear motive(%a)" Term.pp m))
      | _ -> failwith (asprintf "match non-inductive(%a)" Term.pp m))
    | Fix _ -> failwith (asprintf "infer fix(%a)" Term.pp m)
    | Main -> (Knd L, VMap.empty)
    | Proto -> (Knd U, VMap.empty)
    | End -> (Proto, VMap.empty)
    | Inp (a, b) ->
      let x, ub = unbind b in
      let s = infer_sort vctx ictx a in
      let ctx = check (VMap.add x (a, s) vctx) ictx ub Proto in
      if VMap.is_empty ctx then
        (Proto, VMap.empty)
      else
        failwith (asprintf "impure inp(%a)" Term.pp m)
    | Out (a, b) ->
      let x, ub = unbind b in
      let s = infer_sort vctx ictx a in
      let ctx = check (VMap.add x (a, s) vctx) ictx ub Proto in
      if VMap.is_empty ctx then
        (Proto, VMap.empty)
      else
        failwith (asprintf "impure out(%a)" Term.pp m)
    | Ch m ->
      let ctx = check vctx ictx m Proto in
      if VMap.is_empty ctx then
        (Knd L, VMap.empty)
      else
        failwith (asprintf "impure channel(%a)" Term.pp m)
    | Fork (a, m, n) ->
      let x, un = unbind n in
      let ctx1 = check vctx ictx a Proto in
      let ctx2 = check vctx ictx m Main in
      let _, ctx3 = infer (VMap.add x (Ch a, L) vctx) ictx un in
      let a = Ch (dual a) in
      if VMap.is_empty ctx1 then
        (Ind (Prelude.tnsr_id, [ a; Main ]), merge ctx2 ctx3)
      else
        failwith (asprintf "fork impure(%a)" Term.pp a)
    | Send m -> (
      let a, ctx = infer vctx ictx m in
      match whnf a with
      | Ch (Inp (a, b)) ->
        let x, ub = unbind b in
        let b = unbox (bind_var x (lift (Ch ub))) in
        (Pi (L, a, b), ctx)
      | _ -> failwith (asprintf "send on non-inp(%a)" Term.pp m))
    | Recv m -> (
      let a, ctx = infer vctx ictx m in
      match whnf a with
      | Ch (Out (a, b)) ->
        let x, ub = unbind b in
        let b = unbox (bind_var x (lift (Ch ub))) in
        (Ind (Prelude.sig_id, [ a; Lam (U, b) ]), ctx)
      | _ -> failwith (asprintf "recv on non-out(%a)" Term.pp m))
    | Close m -> (
      let a, ctx = infer vctx ictx m in
      match a with
      | Ch End -> (Ind (Prelude.unit_id, []), ctx)
      | _ -> failwith (asprintf "close on non-end(%a)" Term.pp m))
    | Axiom (id, m) ->
      let _ = infer_sort vctx ictx m in
      (m, VMap.empty)

  and infer_pscope = _x

  and check vctx ictx m a = _x
end

module CheckTop = struct end
