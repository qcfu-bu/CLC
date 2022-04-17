open Format
open Bindlib
open Name
open Core
open Term
open Top
open Prelude

let failwith s =
  let _ = printf "%s\n" s in
  failwith "bad"

module Context = struct
  module IMap = Map.Make (Id)

  let find_v x ctx =
    try VMap.find x ctx with
    | _ -> failwith (asprintf "unbound variable(%a)" pp_v x)

  let find_id id ctx =
    try IMap.find id ctx with
    | _ -> failwith (asprintf "unbound ind id(%a)" Id.pp id)

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
    | None -> failwith (asprintf "unbound constr id(%a)" Id.pp id)

  let equal ctx1 ctx2 = VMap.equal (fun _ _ -> true) ctx1 ctx2

  let remove x ctx s =
    match s with
    | U -> ctx
    | L ->
      if VMap.exists (fun y _ -> eq_vars x y) ctx then
        VMap.remove x ctx
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

open Context

module CheckTerm = struct
  let rec dual m =
    let m = whnf m in
    match m with
    | End -> End
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
        failwith (asprintf "impure context(%a)" Term.pp a)
    | a -> failwith (asprintf "unexpected type(%a)" Term.pp a)

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
    | Ind (id, ms) -> (
      let (Top.Ind (_, a, _)) = find_id id ictx in
      try infer_pscope vctx ictx ms a with
      | _ -> failwith (asprintf "ind failure(%a)" Term.pp m))
    | Constr (id, ms) -> (
      let (Top.Constr (_, a)) = find_idc id ictx in
      try infer_pscope vctx ictx ms a with
      | _ -> failwith (asprintf "constr failure(%a)" Term.pp m))
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
                if Term.equal a a' && equal ctx ctx2 then
                  acc
                else
                  failwith "mot0 error")
              (a, merge ctx1 ctx2)
              ctxs)
        | U, Mot1 mt -> (
          let a = subst mt m in
          let ctxs = check_motive cover ictx mot s in
          match ctxs with
          | [] -> (a, ctx1)
          | ctx2 :: ctxs ->
            if VMap.is_empty ctx1 then
              List.fold_left
                (fun acc ctx ->
                  if equal ctx ctx2 then
                    acc
                  else
                    failwith "mot1 error")
                (a, merge ctx1 ctx2)
                ctxs
            else
              failwith "mot1 impure context")
        | _, Mot2 mt -> (
          let a = subst_p mt a in
          let ctxs = check_motive cover ictx mot s in
          match ctxs with
          | [] -> (a, ctx1)
          | ctx2 :: ctxs ->
            List.fold_left
              (fun acc ctx ->
                if equal ctx ctx2 then
                  acc
                else
                  failwith "mot2 error")
              (a, merge ctx1 ctx2)
              ctxs)
        | U, Mot3 mt -> (
          let a = subst_p (subst mt m) a in
          let ctxs = check_motive cover ictx mot s in
          match ctxs with
          | [] -> (a, ctx1)
          | ctx2 :: ctxs ->
            if VMap.is_empty ctx1 then
              List.fold_left
                (fun acc ctx ->
                  if equal ctx ctx2 then
                    acc
                  else
                    failwith "mot3 error")
                (a, merge ctx1 ctx2)
                ctxs
            else
              failwith "mot3 impure context")
        | _ -> failwith (asprintf "linear motive(%a)" Term.pp m))
      | _ -> failwith (asprintf "match non-inductive(%a)" Term.pp m))
    | Fix n -> (
      let _, un = unbind n in
      match un with
      | Ann (_, a) ->
        let _ = infer_sort vctx ictx a in
        let ctx = check vctx ictx m a in
        (a, ctx)
      | _ -> failwith (asprintf "infer fix(%a)" Term.pp m))
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
    | Fork (a, m, n) -> (
      let _ = infer_sort vctx ictx a in
      match whnf a with
      | Ch a ->
        let x, un = unbind n in
        let ctx1 = check vctx ictx a Proto in
        let ctx2 = check vctx ictx m Main in
        let _, ctx3 = infer (VMap.add x (Ch a, L) vctx) ictx un in
        let ctx3 = remove x ctx3 L in
        let a = Ch (dual a) in
        if VMap.is_empty ctx1 then
          (Ind (Prelude.tnsr_id, [ a; Main ]), merge ctx2 ctx3)
        else
          failwith (asprintf "impure fork(%a)" Term.pp a)
      | _ -> failwith (asprintf "non-channel fork(%a)" Term.pp a))
    | Send m -> (
      let a, ctx = infer vctx ictx m in
      match whnf a with
      | Ch (Out (a, b)) ->
        let x, ub = unbind b in
        let b = unbox (bind_var x (lift (Ch ub))) in
        (Pi (L, a, b), ctx)
      | _ -> failwith (asprintf "send on non-out(%a, %a)" Term.pp m Term.pp a))
    | Recv m -> (
      let a, ctx = infer vctx ictx m in
      match whnf a with
      | Ch (Inp (a, b)) ->
        let x, ub = unbind b in
        let b = unbox (bind_var x (lift (Ch ub))) in
        (Ind (Prelude.sig_id, [ a; Lam (U, b) ]), ctx)
      | _ -> failwith (asprintf "recv on non-inp(%a)" Term.pp m))
    | Close m -> (
      let a, ctx = infer vctx ictx m in
      match whnf a with
      | Ch End -> (Ind (Prelude.unit_id, []), ctx)
      | _ -> failwith (asprintf "close on non-end(%a, %a)" Term.pp m Term.pp a))
    | Axiom (id, m) ->
      let _ = infer_sort vctx ictx m in
      (m, VMap.empty)

  and infer_pscope vctx ictx ms a =
    match (ms, a) with
    | m :: ms, PBind (a, b) -> (
      let s = infer_sort vctx ictx a in
      let ctx1 = check vctx ictx m a in
      let a, ctx2 = infer_pscope vctx ictx ms (subst b (Ann (m, a))) in
      match s with
      | U ->
        if VMap.is_empty ctx1 then
          (a, merge ctx1 ctx2)
        else
          failwith "infer pscope impure context"
      | L -> (a, merge ctx1 ctx2))
    | ms, PBase a -> infer_tscope vctx ictx ms a
    | _ -> failwith "infer pscope uneven length"

  and infer_tscope vctx ictx ms a =
    match (ms, a) with
    | m :: ms, TBind (a, b) -> (
      let s = infer_sort vctx ictx a in
      let ctx1 = check vctx ictx m a in
      let a, ctx2 = infer_tscope vctx ictx ms (subst b (Ann (m, a))) in
      match s with
      | U ->
        if VMap.is_empty ctx1 then
          (a, merge ctx1 ctx2)
        else
          failwith "infer tscope impure context"
      | L -> (a, merge ctx1 ctx2))
    | [], TBase a ->
      let _ = infer_sort vctx ictx a in
      (a, VMap.empty)
    | _ -> failwith "infer tscope uneven length"

  and infer_cover cover ictx =
    match cover with
    | (vctx, _, _, ucl, ss) :: cover ->
      let a, ctx = infer vctx ictx ucl in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      (a, ctx) :: infer_cover cover ictx
    | _ -> []

  and coverage vctx ictx cls cs ms =
    let rec t_of_p p =
      match p with
      | PVar x -> Var x
      | PInd (id, ps) -> Ind (id, List.map t_of_p ps)
      | PConstr (id, ps) -> Constr (id, List.map t_of_p ps)
    in
    let strip p =
      match p with
      | PVar x -> x
      | p -> failwith "coverage strip"
    in
    let rec find id cs =
      match cs with
      | (Top.Constr (idc, a) as c) :: cs ->
        if Id.equal id idc then
          (a, cs)
        else
          let b, cs = find id cs in
          (b, c :: cs)
      | _ -> failwith (asprintf "unbound id(%a)" Id.pp id)
    in
    let rec arity_pscope vctx a ms xs =
      match (a, ms) with
      | Top.PBind (a, b), m :: ms ->
        let b = subst b (Ann (m, a)) in
        let vctx, b, ss = arity_pscope vctx b ms xs in
        (vctx, b, ss)
      | Top.PBase a, _ -> arity_tscope vctx a xs
      | _ -> failwith "coverage arity pscope"
    and arity_tscope vctx a xs =
      match (a, xs) with
      | Top.TBind (a, b), x :: xs ->
        let s = infer_sort vctx ictx a in
        let vctx = VMap.add x (a, s) vctx in
        let b = subst b (Var x) in
        let vctx, b, ss = arity_tscope vctx b xs in
        (vctx, b, (x, s) :: ss)
      | Top.TBase a, [] -> (vctx, a, [])
      | _ -> failwith "coverage arity tscope"
    in
    match cls with
    | cl :: cls -> (
      let p, ucl = unbind_p cl in
      match p with
      | PConstr (id, ps) ->
        let xs = List.map strip ps in
        let m = t_of_p p in
        let a, cs = find id cs in
        let vctx, a, ss = arity_pscope vctx a ms xs in
        let cs = coverage vctx ictx cls cs ms in
        (vctx, m, a, ucl, ss) :: cs
      | _ -> failwith "coverage")
    | [] -> (
      match cs with
      | [] -> []
      | _ -> failwith "coverage")

  and check vctx ictx m a =
    match m with
    | Meta x -> failwith (asprintf "check meta(%a)" Meta.pp x)
    | Lam (s, m) as lm -> (
      let x, um = unbind m in
      match whnf a with
      | Pi (t, a, b) when s = t -> (
        let ub = subst b (Var x) in
        let r = infer_sort vctx ictx a in
        let ctx = check (VMap.add x (a, r) vctx) ictx um ub in
        let ctx = remove x ctx r in
        match s with
        | U when VMap.is_empty ctx -> ctx
        | U -> failwith (asprintf "impure context(%a)" Term.pp um)
        | L -> ctx)
      | _ -> failwith (asprintf "type mismatch(%a, %a)" Term.pp lm Term.pp a))
    | Fix m as fx ->
      let x, um = unbind m in
      let s = infer_sort vctx ictx a in
      let ctx = check (VMap.add x (a, s) vctx) ictx um a in
      if VMap.is_empty ctx then
        ctx
      else
        failwith (asprintf "impure context(%a)" Term.pp fx)
    | Let (m, n) ->
      let x, un = unbind n in
      let n = unbox (bind_var x (lift (Ann (un, a)))) in
      let b, ctx = infer vctx ictx (Let (m, n)) in
      check_eq ctx a b
    | Constr (id, ms) -> (
      match whnf a with
      | Ind (_, ns) ->
        let (Top.Constr (_, b)) = find_idc id ictx in
        let b =
          List.fold_left
            (fun a m ->
              match a with
              | Top.PBind (a, b) -> subst b (Ann (m, a))
              | Top.PBase _ -> a)
            b ns
        in
        let b, ctx = infer_pscope vctx ictx ms b in
        check_eq ctx a b
      | _ ->
        let b, ctx = infer vctx ictx m in
        check_eq ctx a b)
    | Match (m, mot, cls) -> (
      match mot with
      | Mot0 -> (
        let b, ctx1 = infer vctx ictx m in
        let b = whnf b in
        match b with
        | Ind (id, ms) -> (
          let (Top.Ind (_, b, cs)) = find_id id ictx in
          let cover = coverage vctx ictx cls cs ms in
          let ctxs = check_cover cover ictx a in
          match ctxs with
          | [] -> ctx1
          | ctx2 :: ctxs ->
            List.fold_left
              (fun acc ctx ->
                if equal ctx ctx2 then
                  acc
                else
                  failwith "mot3 error")
              (merge ctx1 ctx2) ctxs)
        | _ -> failwith (asprintf "check non-inductive(%a)" Term.pp b))
      | _ ->
        let b, ctx = infer vctx ictx (Match (m, mot, cls)) in
        check_eq ctx a b)
    | _ ->
      let b, ctx = infer vctx ictx m in
      check_eq ctx a b

  and check_eq ctx a b =
    if Term.equal a b then
      ctx
    else
      failwith (asprintf "type mismatch(%a, %a)" Term.pp a Term.pp b)

  and check_cover cover ictx a =
    match cover with
    | (vctx, _, _, ucl, ss) :: cover ->
      let ctx = check vctx ictx ucl a in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_cover cover ictx a
    | _ -> []

  and check_motive cover ictx mot s =
    match (mot, s, cover) with
    | Mot0, _, _ -> failwith "check mot0"
    | Mot1 mt, U, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst mt m in
      let ctx = check vctx ictx ucl mt in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_motive cover ictx mot s
    | Mot2 mt, _, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst_p mt a in
      let ctx = check vctx ictx ucl mt in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_motive cover ictx mot s
    | Mot3 mt, U, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst_p (subst mt m) a in
      let ctx = check vctx ictx ucl mt in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_motive cover ictx mot s
    | _ -> []
end

module CheckTop = struct
  let rec infer vctx ictx tp =
    match tp with
    | Main m ->
      let ctx = CheckTerm.check vctx ictx m Term.Main in
      (ctx, ictx)
    | Define (m, tp) ->
      let a, ctx1 = CheckTerm.infer vctx ictx m in
      let s = CheckTerm.infer_sort vctx ictx a in
      let ctx2, ictx =
        if s = U then
          if VMap.is_empty ctx1 then
            infer vctx ictx (subst tp m)
          else
            failwith (asprintf "impure define(%a)" Term.pp m)
        else
          let x, utp = unbind tp in
          let ctx, ictx = infer (VMap.add x (a, s) vctx) ictx utp in
          (remove x ctx s, ictx)
      in
      (merge ctx1 ctx2, ictx)
    | Induct (Ind (id, a, cs), tp) ->
      let _ = check_pscope vctx ictx a U in
      let ictx = IMap.add id (Ind (id, a, [])) ictx in
      let _ =
        List.iter
          (fun (Constr (_, b)) ->
            let _ = check_pscope vctx ictx b U in
            param_pscope b id [])
          cs
      in
      let ictx = IMap.add id (Ind (id, a, cs)) ictx in
      infer vctx ictx tp
    | Import (id, m, tp) ->
      let n =
        if Id.equal id Id.stdin_id then
          Prelude.stdin_t
        else if Id.equal id Id.stdout_id then
          Prelude.stdout_t
        else if Id.equal id Id.stderr_id then
          Prelude.stderr_t
        else
          failwith (asprintf "unknown import id(%a)" Id.pp id)
      in
      let a = Ch (App (n, m)) in
      let ctx1 = CheckTerm.check vctx ictx a (Knd L) in
      let x, utp = unbind tp in
      let ctx2, ictx = infer (VMap.add x (a, L) vctx) ictx utp in
      let ctx2 = remove x ctx2 L in
      (merge ctx1 ctx2, ictx)

  and param_pscope a id xs =
    match a with
    | PBase a -> param_tscope a id (List.rev xs)
    | PBind (_, a) ->
      let x, ua = unbind a in
      param_pscope ua id (x :: xs)

  and param_tscope a id xs =
    let rec param xs ms =
      match (xs, ms) with
      | [], _ -> ()
      | x :: xs, Var y :: ms ->
        if eq_vars x y then
          param xs ms
        else
          failwith (asprintf "unmatched param(%a, %a)" pp_v x pp_v y)
      | _ -> failwith "unmatched param"
    in
    match a with
    | TBase a -> (
      match a with
      | Term.Ind (id', ms) ->
        if Id.equal id id' then
          param xs ms
        else
          failwith (asprintf "unmatched tscope(%a, %a)" Id.pp id Id.pp id')
      | _ -> failwith (asprintf "non-inductive tscope(%a)" Term.pp a))
    | TBind (_, a) ->
      let _, a = unbind a in
      param_tscope a id xs

  and cmp_sort t1 t2 =
    match (t1, t2) with
    | U, L -> false
    | _ -> true

  and min_sort t1 t2 =
    match t1 with
    | U -> t2
    | L -> t1

  and check_pscope vctx ictx a s =
    match a with
    | PBase a -> check_tscope vctx ictx a s
    | PBind (a, b) ->
      let x, ub = unbind b in
      let t = CheckTerm.infer_sort vctx ictx a in
      let vctx = VMap.add x (a, t) vctx in
      check_pscope vctx ictx ub (min_sort s t)

  and check_tscope vctx ictx a s =
    match a with
    | TBase a ->
      let t = CheckTerm.infer_sort vctx ictx a in
      if cmp_sort t s then
        ()
      else
        failwith "unsound tscope"
    | TBind (a, b) ->
      let x, ub = unbind b in
      let t = CheckTerm.infer_sort vctx ictx a in
      let vctx = VMap.add x (a, t) vctx in
      check_tscope vctx ictx ub (min s t)
end

let infer tp =
  let vctx = VMap.singleton Prelude.main_v (Term.Main, L) in
  let ctx, _ = CheckTop.infer vctx IMap.empty tp in
  let ctx = remove Prelude.main_v ctx L in
  if VMap.is_empty ctx then
    ()
  else
    let _ =
      VMap.iter (fun x m -> printf "VMap(%a, %a)@." pp_v x Term.pp m) ctx
    in
    failwith "impure toplevel"
