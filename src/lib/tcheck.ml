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
    | Struct _ -> failwith (asprintf "infer struct(%a)" Term.pp m)
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
    | _ -> _x

  and infer_pscope = _x

  and check vctx ictx m a = _x
end

module CheckTop = struct end
