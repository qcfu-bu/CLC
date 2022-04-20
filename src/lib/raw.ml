open Format
open Bindlib
open Name
open Core

module RTerm = struct
  open Term

  type v = Var.t

  type t =
    (* inference *)
    | Ann of t * t
    | Meta of Meta.t
    (* core *)
    | Knd of sort
    | Var of v
    | Pi of sort * v * t * t
    | Lam of sort * p * t
    | App of t * t
    | Let of p * t * t
    (* inductive *)
    | Ind of Id.t * t list
    | Constr of Id.t * t list
    | Match of t * m * (p * t) list
    | Fix of v * t
    (* session *)
    | Main
    | Proto
    | End
    | Inp of v * t * t
    | Out of v * t * t
    | Dual of t
    | Ch of t
    | Fork of v * t * t * t
    | Send of t
    | Recv of t
    | Close of t
    (* magic *)
    | Axiom of Id.t * t

  and p =
    | PVar of v
    | PInd of Id.t * p list
    | PConstr of Id.t * p list

  and m =
    | Mot0
    | Mot1 of v * t
    | Mot2 of p * t
    | Mot3 of v * p * t

  let var = Var.var (fun x -> Term.Var x)

  let find x ctx =
    try VMap.find x ctx with
    | _ -> failwith (asprintf "desugar cannot find var(%a)" Var.pp x)

  let rec _core ctx m =
    match m with
    | Ann (m, a) ->
      let _m = _core ctx m in
      let _a = _core ctx a in
      _Ann _m _a
    | Meta x -> _Meta x
    | Knd s -> _Knd s
    | Var x ->
      let x = find x ctx in
      _Var x
    | Pi (s, x, a, b) ->
      let _x = var x in
      let _a = _core ctx a in
      let ctx = VMap.add x _x ctx in
      let _b = _core ctx b in
      _Pi s _a (bind_var _x _b)
    | Lam (s, p, m) -> (
      match p with
      | PVar x ->
        let _x = var x in
        let ctx = VMap.add x _x ctx in
        let _m = _core ctx m in
        _Lam s (bind_var _x _m)
      | _ ->
        let _x = mk "x" in
        let _p, ctx = _core_p ctx p in
        let _m = _core ctx m in
        _Lam s
          (bind_var _x (_Match (_Var _x) _Mot0 (box_list [ bind_p _p _m ]))))
    | App (m, n) ->
      let _m = _core ctx m in
      let _n = _core ctx n in
      _App _m _n
    | Let (p, m, n) -> (
      match p with
      | PVar x ->
        let _x = var x in
        let _m = _core ctx m in
        let ctx = VMap.add x _x ctx in
        let _n = _core ctx n in
        _Let _m (bind_var _x _n)
      | _ ->
        let _m = _core ctx m in
        let _p, ctx = _core_p ctx p in
        let _n = _core ctx n in
        _Match _m _Mot0 (box_list [ bind_p _p _n ]))
    | Ind (id, ms) ->
      let _ms = List.map (_core ctx) ms in
      let _ms = box_list _ms in
      _Ind id _ms
    | Constr (id, ms) ->
      let _ms = List.map (_core ctx) ms in
      let _ms = box_list _ms in
      _Constr id _ms
    | Match (m, mot, cls) ->
      let _m = _core ctx m in
      let _mot = _core_m ctx mot in
      let _cls =
        List.map
          (fun (p, b) ->
            let _p, ctx = _core_p ctx p in
            let _b = _core ctx b in
            bind_p _p _b)
          cls
      in
      let _cls = box_list _cls in
      _Match _m _mot _cls
    | Fix (x, m) ->
      let _x = var x in
      let ctx = VMap.add x _x ctx in
      let _m = _core ctx m in
      _Fix (bind_var _x _m)
    | Main -> _Main
    | Proto -> _Proto
    | End -> _End
    | Inp (x, a, b) ->
      let _x = var x in
      let _a = _core ctx a in
      let ctx = VMap.add x _x ctx in
      let _b = _core ctx b in
      _Inp _a (bind_var _x _b)
    | Out (x, a, b) ->
      let _x = var x in
      let _a = _core ctx a in
      let ctx = VMap.add x _x ctx in
      let _b = _core ctx b in
      _Out _a (bind_var _x _b)
    | Dual m ->
      let _m = _core ctx m in
      _Dual _m
    | Ch m ->
      let _m = _core ctx m in
      _Ch _m
    | Fork (x, a, m, n) ->
      let _x = var x in
      let _a = _core ctx a in
      let _m = _core ctx m in
      let ctx = VMap.add x _x ctx in
      let _n = _core ctx n in
      _Fork _a _m (bind_var _x _n)
    | Send m ->
      let _m = _core ctx m in
      _Send _m
    | Recv m ->
      let _m = _core ctx m in
      _Recv _m
    | Close m ->
      let _m = _core ctx m in
      _Close _m
    | Axiom (id, m) ->
      let _m = _core ctx m in
      _Axiom id _m

  and _core_p ctx p =
    match p with
    | PVar x ->
      let _x = var x in
      let ctx = VMap.add x _x ctx in
      (Term.PVar _x, ctx)
    | PInd (id, ps) ->
      let _ps, ctx = _core_ps ctx ps in
      (Term.PInd (id, _ps), ctx)
    | PConstr (id, ps) ->
      let _ps, ctx = _core_ps ctx ps in
      (Term.PConstr (id, _ps), ctx)

  and _core_ps ctx ps =
    match ps with
    | [] -> ([], ctx)
    | p :: ps ->
      let _p, ctx = _core_p ctx p in
      let _ps, ctx = _core_ps ctx ps in
      (_p :: _ps, ctx)

  and _core_m ctx mot =
    match mot with
    | Mot0 -> Term._Mot0
    | Mot1 (x, mot) ->
      let _x = var x in
      let ctx = VMap.add x _x ctx in
      let _mot = _core ctx mot in
      _Mot1 (bind_var _x _mot)
    | Mot2 (p, mot) ->
      let _p, ctx = _core_p ctx p in
      let _mot = _core ctx mot in
      _Mot2 (bind_p _p _mot)
    | Mot3 (x, p, mot) ->
      let _x = var x in
      let ctx = VMap.add x _x ctx in
      let _p, ctx = _core_p ctx p in
      let _mot = _core ctx mot in
      _Mot3 (bind_var _x (bind_p _p _mot))

  let core ctx m = unbox (_core ctx m)
end

module RTop = struct
  open Top
  open RTerm

  exception EmptyTop

  exception AppendMain

  type v = Var.t

  type ind = Ind of Id.t * pscope * constr list

  and constr = Constr of Id.t * pscope

  and pscope =
    | PBase of tscope
    | PBind of v * RTerm.t * pscope

  and tscope =
    | TBase of RTerm.t
    | TBind of v * RTerm.t * tscope

  type t =
    | Empty
    | Main of RTerm.t
    | Define of v * RTerm.t * t
    | Induct of ind * t
    | Import of Id.t * RTerm.t * v * t

  let rec append_t t1 t2 =
    match t1 with
    | Empty -> t2
    | Main _ -> raise AppendMain
    | Define (v, m, t1) -> Define (v, m, append_t t1 t2)
    | Induct (ind, t1) -> Induct (ind, append_t t1 t2)
    | Import (id, m, x, t1) -> Import (id, m, x, append_t t1 t2)

  let rec _core ctx t =
    match t with
    | Empty -> raise EmptyTop
    | Main m ->
      let _m = RTerm._core ctx m in
      _Main _m
    | Define (x, m, t) ->
      let _x = var x in
      let _m = RTerm._core ctx m in
      let ctx = VMap.add x _x ctx in
      let _t = _core ctx t in
      _Define _m (bind_var _x _t)
    | Induct (Ind (id, a, cs), t) ->
      let _a = _core_pscope ctx a in
      let _cs = List.map (_core_constr ctx) cs in
      let _cs = box_list _cs in
      let _t = _core ctx t in
      _Induct (_Ind id _a _cs) _t
    | Import (id, m, x, t) ->
      let _x = var x in
      let _m = RTerm._core ctx m in
      let ctx = VMap.add x _x ctx in
      let _t = _core ctx t in
      _Import id _m (bind_var _x _t)

  and _core_pscope ctx a =
    match a with
    | PBase a ->
      let _a = _core_tscope ctx a in
      _PBase _a
    | PBind (x, a, b) ->
      let _x = var x in
      let _a = RTerm._core ctx a in
      let ctx = VMap.add x _x ctx in
      let _b = _core_pscope ctx b in
      _PBind _a (bind_var _x _b)

  and _core_tscope ctx a =
    match a with
    | TBase a ->
      let _a = RTerm._core ctx a in
      _TBase _a
    | TBind (x, a, b) ->
      let _x = var x in
      let _a = RTerm._core ctx a in
      let ctx = VMap.add x _x ctx in
      let _b = _core_tscope ctx b in
      _TBind _a (bind_var _x _b)

  and _core_constr ctx (Constr (id, a)) =
    let _a = _core_pscope ctx a in
    _Constr id _a

  let main = var Var.main

  let core t =
    let ctx = VMap.singleton Var.main main in
    unbox (_core ctx t)
end