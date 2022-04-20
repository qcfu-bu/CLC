open Format
open Bindlib
open Name
open Core
open Term
open Top
open Context
open Prelude
open Unify

let failwith s =
  let _ = printf "%s\n" s in
  failwith "bad"

module ElabTerm = struct
  let rec infer_sort vctx ictx eqns mmap m =
    let a, eqns, mmap = infer vctx ictx eqns mmap m in
    match whnf a with
    | Knd s -> (s, eqns, mmap)
    | _ -> failwith (asprintf "unexpected type(%a)" Term.pp a)

  and infer vctx ictx eqns mmap m =
    let h, _ = spine m in
    match h with
    | Meta _ ->
      let xs = List.map fst (VMap.bindings vctx) in
      let a = _mApp (_Meta (Meta.mk ())) (List.map _Var xs) in
      (unbox a, eqns, mmap)
    | _ -> (
      match m with
      | Ann (m, a) -> (
        let _, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        match m with
        | Let (m, n) ->
          let x, un = unbind n in
          let n = unbox (bind_var x (lift (Ann (un, a)))) in
          let eqns, mmap = check vctx ictx eqns mmap (Let (m, n)) a in
          (a, eqns, mmap)
        | _ ->
          let eqns, mmap = check vctx ictx eqns mmap m a in
          (a, eqns, mmap))
      | Meta x -> failwith (asprintf "infer meta(%a)" Meta.pp x)
      | Knd _ -> (Knd U, eqns, mmap)
      | Var x ->
        let a, _ = find_v x vctx in
        (a, eqns, mmap)
      | Pi (s, a, b) ->
        let x, ub = unbind b in
        let t, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        let _, eqns, mmap =
          infer_sort (VMap.add x (a, t) vctx) ictx eqns mmap ub
        in
        (Knd s, eqns, mmap)
      | Lam _ -> (Meta (Meta.mk ()), eqns, mmap)
      | App (m, n) -> (
        let a, eqns, mmap = infer vctx ictx eqns mmap m in
        match whnf a with
        | Pi (_, a, b) ->
          let t, eqns, mmap = infer_sort vctx ictx eqns mmap a in
          let eqns, mmap = check vctx ictx eqns mmap n a in
          (subst b n, eqns, mmap)
        | _ -> failwith (asprintf "infer app(%a)" Term.pp m))
      | Let (m, n) ->
        let a, eqns, mmap = infer vctx ictx eqns mmap m in
        let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        let mmap = unify mmap eqns in
        let m = UnifyTerm.resolve mmap m in
        let a = UnifyTerm.resolve mmap a in
        let b, eqns, mmap =
          match s with
          | U -> infer vctx ictx eqns mmap (subst n m)
          | L ->
            let x, un = unbind n in
            infer (VMap.add x (a, s) vctx) ictx eqns mmap un
        in
        (b, eqns, mmap)
      | Ind (id, ms) -> (
        let (Top.Ind (_, a, _)) = find_id id ictx in
        try infer_pscope vctx ictx eqns mmap ms a with
        | _ -> failwith (asprintf "ind failure(%a)" Term.pp m))
      | Constr (id, ms) -> (
        let (Top.Constr (_, a)) = find_idc id ictx in
        try infer_pscope vctx ictx eqns mmap ms a with
        | _ -> failwith (asprintf "constr failure(%a)" Term.pp m))
      | Match (m, mot, cls) -> (
        let a, eqns, mmap = infer vctx ictx eqns mmap m in
        let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        let a = whnf a in
        match a with
        | Ind (id, ms) -> (
          let (Top.Ind (_, _, cs)) = find_id id ictx in
          let cover, eqns, mmap = coverage vctx ictx eqns mmap cls cs ms in
          match (s, mot) with
          | _, Mot0 -> (
            let ms, eqns, mmap = infer_cover cover ictx eqns mmap in
            match ms with
            | [] -> failwith "infer motive error"
            | m :: ms ->
              let eqns = List.fold_left (fun acc n -> (m, n) :: acc) eqns ms in
              (m, eqns, mmap))
          | U, Mot1 mt ->
            let a = subst mt m in
            let eqns, mmap = check_motive cover ictx eqns mmap mot s in
            (a, eqns, mmap)
          | _, Mot2 mt ->
            let a = subst_p mt a in
            let eqns, mmap = check_motive cover ictx eqns mmap mot s in
            (a, eqns, mmap)
          | U, Mot3 mt ->
            let a = subst_p (subst mt m) a in
            let eqns, mmap = check_motive cover ictx eqns mmap mot s in
            (a, eqns, mmap)
          | _ -> failwith (asprintf "linear motive(%a)" Term.pp m))
        | _ -> failwith (asprintf "match non-inductive(%a)" Term.pp m))
      | Fix n -> (
        let _, un = unbind n in
        match un with
        | Ann (_, a) ->
          let _, eqns, mmap = infer_sort vctx ictx eqns mmap a in
          let eqns, mmap = check vctx ictx eqns mmap m a in
          (a, eqns, mmap)
        | _ -> (Meta (Meta.mk ()), eqns, mmap))
      | Main -> (Knd L, eqns, mmap)
      | Proto -> (Knd U, eqns, mmap)
      | End -> (Proto, eqns, mmap)
      | Inp (a, b) ->
        let x, ub = unbind b in
        let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        let eqns, mmap =
          check (VMap.add x (a, s) vctx) ictx eqns mmap ub Proto
        in
        (Proto, eqns, mmap)
      | Out (a, b) ->
        let x, ub = unbind b in
        let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        let eqns, mmap =
          check (VMap.add x (a, s) vctx) ictx eqns mmap ub Proto
        in
        (Proto, eqns, mmap)
      | Ch m ->
        let eqns, mmap = check vctx ictx eqns mmap m Proto in
        (Knd L, eqns, mmap)
      | Fork (a, m, n) -> (
        let _, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        match whnf a with
        | Ch a ->
          let x, un = unbind n in
          let eqns, mmap = check vctx ictx eqns mmap a Proto in
          let eqns, mmap = check vctx ictx eqns mmap m Main in
          let _, eqns, mmap =
            infer (VMap.add x (Ch a, L) vctx) ictx eqns mmap un
          in
          let a = Ch (Dual a) in
          (Ind (Prelude.tnsr_id, [ a; Main ]), eqns, mmap)
        | _ -> failwith (asprintf "non-channel fork(%a)" Term.pp a))
      | Send m -> (
        let a, eqns, mmap = infer vctx ictx eqns mmap m in
        match whnf a with
        | Ch (Out (a, b)) ->
          let x, ub = unbind b in
          let b = unbox (bind_var x (lift (Ch ub))) in
          (Pi (L, a, b), eqns, mmap)
        | _ -> failwith (asprintf "send on non-out(%a, %a)" Term.pp m Term.pp a)
        )
      | Recv m -> (
        let a, eqns, mmap = infer vctx ictx eqns mmap m in
        match whnf a with
        | Ch (Inp (a, b)) -> (
          let x, ub = unbind b in
          let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
          match s with
          | U ->
            let b = unbox (bind_var x (lift (Ch ub))) in
            (Ind (Prelude.sig_id, [ a; Lam (U, b) ]), eqns, mmap)
          | L -> (Ind (Prelude.tnsr_id, [ a; Ch ub ]), eqns, mmap))
        | _ -> failwith (asprintf "recv on non-inp(%a, %a)" Term.pp m Term.pp a)
        )
      | Close m -> (
        let a, eqns, mmap = infer vctx ictx eqns mmap m in
        match whnf a with
        | Ch End -> (Ind (Prelude.unit_id, []), eqns, mmap)
        | _ ->
          failwith (asprintf "close on non-end(%a, %a)" Term.pp m Term.pp a))
      | Dual m ->
        let eqns, mmap = check vctx ictx eqns mmap m Proto in
        (Proto, eqns, mmap)
      | Axiom (id, m) ->
        let _, eqns, mmap = infer_sort vctx ictx eqns mmap m in
        (m, eqns, mmap))

  and infer_pscope vctx ictx eqns mmap ms a =
    match (ms, a) with
    | m :: ms, PBind (a, b) ->
      let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
      let eqns, mmap = check vctx ictx eqns mmap m a in
      infer_pscope vctx ictx eqns mmap ms (subst b (Ann (m, a)))
    | ms, PBase a -> infer_tscope vctx ictx eqns mmap ms a
    | _ -> failwith "infer pscope uneven length"

  and infer_tscope vctx ictx eqns mmap ms a =
    match (ms, a) with
    | m :: ms, TBind (a, b) ->
      let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
      let eqns, mmap = check vctx ictx eqns mmap m a in
      infer_tscope vctx ictx eqns mmap ms (subst b (Ann (m, a)))
    | [], TBase a ->
      let _, eqns, mmap = infer_sort vctx ictx eqns mmap a in
      (a, eqns, mmap)
    | _ -> failwith "infer tscope uneven length"

  and infer_cover cover ictx eqns mmap =
    match cover with
    | (vctx, _, _, ucl, ss) :: cover ->
      let m, eqns, mmap = infer vctx ictx eqns mmap ucl in
      let ms, eqns, mmap = infer_cover cover ictx eqns mmap in
      (m :: ms, eqns, mmap)
    | _ -> ([], eqns, mmap)

  and coverage vctx ictx eqns mmap cls cs ms =
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
    let rec arity_pscope vctx eqns mmap a ms xs =
      match (a, ms) with
      | Top.PBind (a, b), m :: ms ->
        let b = subst b (Ann (m, a)) in
        arity_pscope vctx eqns mmap b ms xs
      | Top.PBase a, _ -> arity_tscope vctx a xs
      | _ -> failwith "coverage arity pscope"
    and arity_tscope vctx a xs =
      match (a, xs) with
      | Top.TBind (a, b), x :: xs ->
        let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        let vctx = VMap.add x (a, s) vctx in
        let b = subst b (Var x) in
        let vctx, b, ss, eqns, mmap = arity_tscope vctx b xs in
        (vctx, b, (x, s) :: ss, eqns, mmap)
      | Top.TBase a, [] -> (vctx, a, [], eqns, mmap)
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
        let vctx, a, ss, eqns, mmap = arity_pscope vctx eqns mmap a ms xs in
        let cs, eqns, mmap = coverage vctx ictx eqns mmap cls cs ms in
        ((vctx, m, a, ucl, ss) :: cs, eqns, mmap)
      | _ -> failwith "coverage")
    | [] -> (
      match cs with
      | [] -> ([], eqns, mmap)
      | _ -> failwith "coverage")

  and check vctx ictx eqns mmap m a =
    match m with
    | Meta _ -> (eqns, mmap)
    | Lam (s, m) as lm -> (
      let x, um = unbind m in
      match whnf a with
      | Pi (t, a, b) when s = t ->
        let ub = subst b (Var x) in
        let r, eqns, mmap = infer_sort vctx ictx eqns mmap a in
        check (VMap.add x (a, r) vctx) ictx eqns mmap um ub
      | _ -> failwith (asprintf "type mismatch(%a, %a)" Term.pp lm Term.pp a))
    | Fix m ->
      let x, um = unbind m in
      let s, eqns, mmap = infer_sort vctx ictx eqns mmap a in
      check (VMap.add x (a, s) vctx) ictx eqns mmap um a
    | Let (m, n) ->
      let x, un = unbind n in
      let n = unbox (bind_var x (lift (Ann (un, a)))) in
      let b, eqns, mmap = infer vctx ictx eqns mmap (Let (m, n)) in
      check_eq eqns mmap a b
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
        let b, eqns, mmap = infer_pscope vctx ictx eqns mmap ms b in
        check_eq eqns mmap a b
      | _ ->
        let b, eqns, mmap = infer vctx ictx eqns mmap m in
        check_eq eqns mmap a b)
    | Match (m, mot, cls) -> (
      match mot with
      | Mot0 -> (
        let b, eqns, mmap = infer vctx ictx eqns mmap m in
        let b = whnf b in
        match b with
        | Ind (id, ms) ->
          let (Top.Ind (_, b, cs)) = find_id id ictx in
          let cover, eqns, mmap = coverage vctx ictx eqns mmap cls cs ms in
          check_cover cover ictx eqns mmap a
        | _ -> failwith (asprintf "check non-inductive(%a)" Term.pp b))
      | _ ->
        let b, eqns, mmap = infer vctx ictx eqns mmap (Match (m, mot, cls)) in
        check_eq eqns mmap a b)
    | _ ->
      let b, eqns, mmap = infer vctx ictx eqns mmap m in
      check_eq eqns mmap a b

  and check_eq eqns mmap a b = ((a, b) :: eqns, mmap)

  and check_cover cover ictx eqns mmap a =
    match cover with
    | (vctx, _, _, ucl, ss) :: cover ->
      let eqns, mmap = check vctx ictx eqns mmap ucl a in
      check_cover cover ictx eqns mmap a
    | _ -> (eqns, mmap)

  and check_motive cover ictx eqns mmap mot s =
    match (mot, s, cover) with
    | Mot0, _, _ -> failwith "check mot0"
    | Mot1 mt, U, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst mt m in
      let eqns, mmap = check vctx ictx eqns mmap ucl mt in
      check_motive cover ictx eqns mmap mot s
    | Mot2 mt, _, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst_p mt a in
      let eqns, mmap = check vctx ictx eqns mmap ucl mt in
      check_motive cover ictx eqns mmap mot s
    | Mot3 mt, U, (vctx, m, a, ucl, ss) :: cover ->
      let mt = subst_p (subst mt m) a in
      let eqns, mmap = check vctx ictx eqns mmap ucl mt in
      check_motive cover ictx eqns mmap mot s
    | _ -> (eqns, mmap)
end

module ElabTop = struct
  let rec infer vctx ictx eqns mmap tp =
    match tp with
    | Main m ->
      let eqns, mmap = ElabTerm.check vctx ictx eqns mmap m Term.Main in
      let mmap = unify mmap eqns in
      (ictx, mmap)
    | Define (m, tp) ->
      let a, eqns, mmap = ElabTerm.infer vctx ictx eqns mmap m in
      let s, eqns, mmap = ElabTerm.infer_sort vctx ictx eqns mmap a in
      let mmap = unify mmap eqns in
      let m = UnifyTerm.resolve mmap m in
      let a = UnifyTerm.resolve mmap a in
      if s = U then
        infer vctx ictx eqns mmap (subst tp m)
      else
        let x, utp = unbind tp in
        infer (VMap.add x (a, s) vctx) ictx eqns mmap utp
    | Induct (Ind (id, a, cs), tp) ->
      let eqns, mmap = check_pscope vctx ictx eqns mmap a U in
      let mmap = unify mmap eqns in
      let a = unbox (UnifyTop.resolve_pscope mmap a) in
      let ictx = IMap.add id (Ind (id, a, [])) ictx in
      let eqns, mmap =
        List.fold_left
          (fun (eqns, mmap) (Constr (_, b)) ->
            let eqns, mmap = check_pscope vctx ictx eqns mmap b U in
            let _ = param_pscope b id [] in
            (eqns, mmap))
          (eqns, mmap) cs
      in
      let mmap = unify mmap eqns in
      let cs = List.map (fun x -> unbox (UnifyTop.resolve_constr mmap x)) cs in
      let ictx = IMap.add id (Ind (id, a, cs)) ictx in
      infer vctx ictx eqns mmap tp
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
      let eqns, mmap = ElabTerm.check vctx ictx eqns mmap a (Knd L) in
      let x, utp = unbind tp in
      infer (VMap.add x (a, L) vctx) ictx eqns mmap utp

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

  and check_pscope vctx ictx eqns mmap a s =
    match a with
    | PBase a -> check_tscope vctx ictx eqns mmap a s
    | PBind (a, b) ->
      let x, ub = unbind b in
      let t, eqns, mmap = ElabTerm.infer_sort vctx ictx eqns mmap a in
      let vctx = VMap.add x (a, t) vctx in
      check_pscope vctx ictx eqns mmap ub (min_sort s t)

  and check_tscope vctx ictx eqns mmap a s =
    match a with
    | TBase a ->
      let t, eqns, mmap = ElabTerm.infer_sort vctx ictx eqns mmap a in
      if cmp_sort t s then
        (eqns, mmap)
      else
        failwith "unsound tscope"
    | TBind (a, b) ->
      let x, ub = unbind b in
      let t, eqns, mmap = ElabTerm.infer_sort vctx ictx eqns mmap a in
      let vctx = VMap.add x (a, t) vctx in
      check_tscope vctx ictx eqns mmap ub (min s t)
end

let elab tp =
  let vctx = VMap.singleton Prelude.main_v (Term.Main, L) in
  let _, mmap = ElabTop.infer vctx IMap.empty [] MMap.empty tp in
  unbox (UnifyTop.resolve mmap tp)