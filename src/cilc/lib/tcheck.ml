open Format
open Bindlib
open Name
open Core
open Tm
open Tp
open Context
open Prelude

let failwith s =
  let _ = printf "%s\n" s in
  failwith "tcheck"

module CheckTm = struct
  let rec infer_sort vctx ictx env m =
    let a, ctx = infer vctx ictx env m in
    match zdnf env a with
    | Knd s ->
      if VMap.is_empty ctx then
        s
      else
        failwith (asprintf "impure context(%a)" Tm.pp a)
    | a -> failwith (asprintf "unexpected type(%a)" Tm.pp a)

  and infer vctx ictx env m =
    match m with
    | Ann (m, a) -> (
      let _ = infer_sort vctx ictx env a in
      match m with
      | Let (m, n) ->
        let x, un = unbind n in
        let n = unbox (bind_var x (lift (Ann (un, a)))) in
        let ctx = check vctx ictx env (Let (m, n)) a in
        (a, ctx)
      | _ ->
        let ctx = check vctx ictx env m a in
        (a, ctx))
    | Meta (x, _) -> failwith (asprintf "infer meta(%a)" Meta.pp x)
    | Knd _ -> (Knd U, VMap.empty)
    | Var x -> (
      let a, s = find_v x vctx in
      match s with
      | U -> (a, VMap.empty)
      | L -> (a, VMap.singleton x a))
    | Pi (s, a, b) ->
      let x, ub = unbind b in
      let t = infer_sort vctx ictx env a in
      let _ = infer_sort (VMap.add x (a, t) vctx) ictx env ub in
      (Knd s, VMap.empty)
    | Lam _ -> failwith (asprintf "infer lam(%a)" Tm.pp m)
    | App (m, n) -> (
      let a, ctx1 = infer vctx ictx env m in
      match zdnf env a with
      | Pi (s, a, b) -> (
        let t = infer_sort vctx ictx env a in
        let ctx2 = check vctx ictx env n a in
        match t with
        | U ->
          if VMap.is_empty ctx2 then
            (subst b (Ann (n, a)), merge ctx1 ctx2)
          else
            failwith (asprintf "impure arg(%a)" Tm.pp n)
        | L -> (subst b (Ann (n, a)), merge ctx1 ctx2))
      | _ -> failwith (asprintf "infer app(%a)" Tm.pp m))
    | Let (m, n) ->
      let a, ctx1 = infer vctx ictx env m in
      let s = infer_sort vctx ictx env a in
      let b, ctx2 =
        match s with
        | U when VMap.is_empty ctx1 ->
          let x, un = unbind n in
          infer (VMap.add x (a, s) vctx) ictx (VMap.add x m env) un
        | U -> failwith (asprintf "impure let(%a)" Tm.pp m)
        | L ->
          let x, un = unbind n in
          let b, ctx2 = infer (VMap.add x (a, s) vctx) ictx env un in
          (b, remove x ctx2 s)
      in
      (b, merge ctx1 ctx2)
    | Ind (id, ms) -> (
      let (Tp.Ind (_, a, _)) = find_id id ictx in
      try infer_pscope vctx ictx env ms a with
      | _ -> failwith (asprintf "ind failure(%a)" Tm.pp m))
    | Constr (id, ms) -> (
      let (Tp.Constr (_, a)) = find_idc id ictx in
      try infer_pscope vctx ictx env ms a with
      | _ -> failwith (asprintf "constr failure(%a)" Tm.pp m))
    | Match (m, mot, cls) -> (
      let a, ctx1 = infer vctx ictx env m in
      let s = infer_sort vctx ictx env a in
      let a = zdnf env a in
      match a with
      | Ind (id, ms) -> (
        let (Tp.Ind (_, _, cs)) = find_id id ictx in
        let cover = coverage vctx ictx env cls cs ms in
        match (s, mot) with
        | _, Mot0 -> (
          let ctxs = infer_cover cover ictx env in
          match ctxs with
          | [] -> failwith "infer motive error"
          | (a, ctx2) :: ctxs ->
            List.fold_left
              (fun acc (a', ctx) ->
                if Tm.equal env a a' && equal ctx ctx2 then
                  acc
                else
                  failwith "mot0 error")
              (a, merge ctx1 ctx2)
              ctxs)
        | U, Mot1 mt -> (
          let a = subst mt m in
          let ctxs = check_motive cover ictx env mot s in
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
          let ctxs = check_motive cover ictx env mot s in
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
          let ctxs = check_motive cover ictx env mot s in
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
        | _ -> failwith (asprintf "linear motive(%a)" Tm.pp m))
      | _ -> failwith (asprintf "match non-inductive(%a)" Tm.pp m))
    | Fix n -> (
      let _, un = unbind n in
      match un with
      | Ann (_, a) ->
        let _ = infer_sort vctx ictx env a in
        let ctx = check vctx ictx env m a in
        (a, ctx)
      | _ -> failwith (asprintf "infer fix(%a)" Tm.pp m))
    | Axiom (id, m) ->
      let _ = infer_sort vctx ictx env m in
      (m, VMap.empty)

  and infer_pscope vctx ictx env ms a =
    match (ms, a) with
    | m :: ms, PBind (a, b) -> (
      let s = infer_sort vctx ictx env a in
      let ctx1 = check vctx ictx env m a in
      let a, ctx2 = infer_pscope vctx ictx env ms (subst b (Ann (m, a))) in
      match s with
      | U ->
        if VMap.is_empty ctx1 then
          (a, merge ctx1 ctx2)
        else
          failwith "infer pscope impure context"
      | L -> (a, merge ctx1 ctx2))
    | ms, PBase a -> infer_tscope vctx ictx env ms a
    | _ -> failwith "infer pscope uneven length"

  and infer_tscope vctx ictx env ms a =
    match (ms, a) with
    | m :: ms, TBind (a, b) -> (
      let s = infer_sort vctx ictx env a in
      let ctx1 = check vctx ictx env m a in
      let a, ctx2 = infer_tscope vctx ictx env ms (subst b (Ann (m, a))) in
      match s with
      | U ->
        if VMap.is_empty ctx1 then
          (a, merge ctx1 ctx2)
        else
          failwith "infer tscope impure context"
      | L -> (a, merge ctx1 ctx2))
    | [], TBase a ->
      let _ = infer_sort vctx ictx env a in
      (a, VMap.empty)
    | _ -> failwith "infer tscope uneven length"

  and infer_cover cover ictx env =
    match cover with
    | (vctx, _, _, ucl, ss) :: cover ->
      let a, ctx = infer vctx ictx env ucl in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      (a, ctx) :: infer_cover cover ictx env
    | _ -> []

  and coverage vctx ictx env cls cs ms =
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
      | (Tp.Constr (idc, a) as c) :: cs ->
        if Id.equal id idc then
          (a, cs)
        else
          let b, cs = find id cs in
          (b, c :: cs)
      | _ -> failwith (asprintf "unbound id(%a)" Id.pp id)
    in
    let rec arity_pscope vctx a ms xs =
      match (a, ms) with
      | Tp.PBind (a, b), m :: ms ->
        let b = subst b (Ann (m, a)) in
        arity_pscope vctx b ms xs
      | Tp.PBase a, _ -> arity_tscope vctx a xs
      | _ -> failwith "coverage arity pscope"
    and arity_tscope vctx a xs =
      match (a, xs) with
      | Tp.TBind (a, b), x :: xs ->
        let s = infer_sort vctx ictx env a in
        let vctx = VMap.add x (a, s) vctx in
        let b = subst b (Var x) in
        let vctx, b, ss = arity_tscope vctx b xs in
        (vctx, b, (x, s) :: ss)
      | Tp.TBase a, [] -> (vctx, a, [])
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
        let cs = coverage vctx ictx env cls cs ms in
        (vctx, m, a, ucl, ss) :: cs
      | _ -> failwith "coverage")
    | [] -> (
      match cs with
      | [] -> []
      | _ -> failwith "coverage")

  and check vctx ictx env m a =
    match m with
    | Meta (x, _) -> failwith (asprintf "check meta(%a)" Meta.pp x)
    | Lam (s, m) as lm -> (
      let x, um = unbind m in
      match zdnf env a with
      | Pi (t, a, b) when s = t -> (
        let ub = subst b (Var x) in
        let r = infer_sort vctx ictx env a in
        let ctx = check (VMap.add x (a, r) vctx) ictx env um ub in
        let ctx = remove x ctx r in
        match s with
        | U when VMap.is_empty ctx -> ctx
        | U -> failwith (asprintf "impure context(%a)" Tm.pp um)
        | L -> ctx)
      | _ -> failwith (asprintf "type mismatch(%a, %a)" Tm.pp lm Tm.pp a))
    | Fix m as fx ->
      let x, um = unbind m in
      let s = infer_sort vctx ictx env a in
      let ctx = check (VMap.add x (a, s) vctx) ictx env um a in
      if VMap.is_empty ctx then
        ctx
      else
        failwith (asprintf "impure context(%a)" Tm.pp fx)
    | Let (m, n) ->
      let x, un = unbind n in
      let n = unbox (bind_var x (lift (Ann (un, a)))) in
      let b, ctx = infer vctx ictx env (Let (m, n)) in
      check_eq env ctx a b
    | Constr (id, ms) -> (
      match zdnf env a with
      | Ind (_, ns) ->
        let (Tp.Constr (_, b)) = find_idc id ictx in
        let b =
          List.fold_left
            (fun a m ->
              match a with
              | Tp.PBind (a, b) -> subst b (Ann (m, a))
              | Tp.PBase _ -> a)
            b ns
        in
        let b, ctx = infer_pscope vctx ictx env ms b in
        check_eq env ctx a b
      | _ ->
        let b, ctx = infer vctx ictx env m in
        check_eq env ctx a b)
    | Match (m, mot, cls) -> (
      match mot with
      | Mot0 -> (
        let b, ctx1 = infer vctx ictx env m in
        let b = zdnf env b in
        match b with
        | Ind (id, ms) -> (
          let (Tp.Ind (_, b, cs)) = find_id id ictx in
          let cover = coverage vctx ictx env cls cs ms in
          let ctxs = check_cover cover ictx env a in
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
        | _ -> failwith (asprintf "check non-inductive(%a)" Tm.pp b))
      | _ ->
        let b, ctx = infer vctx ictx env (Match (m, mot, cls)) in
        check_eq env ctx a b)
    | _ ->
      let b, ctx = infer vctx ictx env m in
      check_eq env ctx a b

  and check_eq env ctx a b =
    if Tm.equal env a b then
      ctx
    else
      failwith (asprintf "type mismatch(%a, %a)" Tm.pp a Tm.pp b)

  and check_cover cover ictx env a =
    match cover with
    | (vctx, _, _, ucl, ss) :: cover ->
      let ctx = check vctx ictx env ucl a in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_cover cover ictx env a
    | _ -> []

  and check_motive cover ictx env mot s =
    match (mot, s, cover) with
    | Mot0, _, _ -> failwith "check mot0"
    | Mot1 mt, U, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst mt m in
      let ctx = check vctx ictx env ucl mt in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_motive cover ictx env mot s
    | Mot2 mt, _, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst_p mt a in
      let ctx = check vctx ictx env ucl mt in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_motive cover ictx env mot s
    | Mot3 mt, U, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst_p (subst mt m) a in
      let ctx = check vctx ictx env ucl mt in
      let ctx = List.fold_left (fun ctx (x, s) -> remove x ctx s) ctx ss in
      ctx :: check_motive cover ictx env mot s
    | _ -> []
end

module CheckTp = struct
  let rec infer vctx ictx env tp =
    match tp with
    | Main m ->
      let ctx = CheckTm.check vctx ictx env m (Tm.Ind (Prelude.unit_id, [])) in
      (ctx, ictx)
    | Define (m, tp) ->
      let a, ctx1 = CheckTm.infer vctx ictx env m in
      let s = CheckTm.infer_sort vctx ictx env a in
      let ctx2, ictx =
        if s = U then
          if VMap.is_empty ctx1 then
            let x, utp = unbind tp in
            infer (VMap.add x (a, s) vctx) ictx (VMap.add x m env) utp
          else
            failwith (asprintf "impure define(%a)" Tm.pp m)
        else
          let x, utp = unbind tp in
          let ctx, ictx = infer (VMap.add x (a, s) vctx) ictx env utp in
          (remove x ctx s, ictx)
      in
      (merge ctx1 ctx2, ictx)
    | Induct (Ind (id, a, cs), tp) ->
      let _ = check_pscope vctx ictx env a U in
      let ictx = IMap.add id (Ind (id, a, [])) ictx in
      let _ =
        List.iter
          (fun (Constr (_, b)) ->
            let _ = check_pscope vctx ictx env b U in
            param_pscope b id [])
          cs
      in
      let ictx = IMap.add id (Ind (id, a, cs)) ictx in
      infer vctx ictx env tp

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
      | Tm.Ind (id', ms) ->
        if Id.equal id id' then
          param xs ms
        else
          failwith (asprintf "unmatched tscope(%a, %a)" Id.pp id Id.pp id')
      | _ -> failwith (asprintf "non-inductive tscope(%a)" Tm.pp a))
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

  and check_pscope vctx ictx env a s =
    match a with
    | PBase a -> check_tscope vctx ictx env a s
    | PBind (a, b) ->
      let x, ub = unbind b in
      let t = CheckTm.infer_sort vctx ictx env a in
      let vctx = VMap.add x (a, t) vctx in
      check_pscope vctx ictx env ub (min_sort s t)

  and check_tscope vctx ictx env a s =
    match a with
    | TBase a ->
      let t = CheckTm.infer_sort vctx ictx env a in
      if cmp_sort t s then
        ()
      else
        failwith "unsound tscope"
    | TBind (a, b) ->
      let x, ub = unbind b in
      let t = CheckTm.infer_sort vctx ictx env a in
      let vctx = VMap.add x (a, t) vctx in
      check_tscope vctx ictx env ub (min s t)
end

let infer tp =
  let ctx, _ = CheckTp.infer VMap.empty IMap.empty VMap.empty tp in
  if VMap.is_empty ctx then
    ()
  else
    let _ = VMap.iter (fun x m -> printf "VMap(%a, %a)@." pp_v x Tm.pp m) ctx in
    failwith "impure toplevel"
