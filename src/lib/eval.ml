open Bindlib
open Name
open Core
open Thread
open Event

module EvalTerm = struct
  open Term

  exception NonFunctionalApp

  exception UnMatchedPattern

  exception NonChannelError

  type value =
    | VBox
    | VConstr of Id.t * value list
    | VLam of Term.v * Term.t
    | VFix of Term.v * Term.t
    | VCh of value channel
    | VSend of value channel

  type env = value VMap.t

  let rec mt_of_pt0 p0 v =
    match (p0, v) with
    | P0Rel, _ -> [| v |]
    | P0Ind _, _ -> raise PBacktrack
    | P0Constr (id1, ps), VConstr (id2, ms) ->
      if Id.equal id1 id2 then
        List.fold_left2
          (fun acc p t -> Array.append acc (mt_of_pt0 p t))
          [||] ps ms
      else
        raise PBacktrack
    | _ -> raise PBacktrack

  let rec mk_env env p m =
    match (p, m) with
    | PVar x, m -> VMap.add x m env
    | PInd _, _ -> raise PBacktrack
    | PConstr (id1, ps), VConstr (id2, ms) ->
      if Id.equal id1 id2 then
        List.fold_left2 (fun acc p m -> mk_env acc p m) env ps ms
      else
        raise PBacktrack
    | _ -> raise PBacktrack

  let rec eval env m =
    match m with
    | Ann (m, _) -> eval env m
    | Meta _ -> VBox
    | Knd _ -> VBox
    | Var x -> (
      try VMap.find x env with
      | _ -> failwith (Format.asprintf "cannot find %a" pp_v x))
    | Pi _ -> VBox
    | Lam (_, m) ->
      let x, um = unbind m in
      VLam (x, um)
    | App (m, n) -> (
      let m = eval env m in
      match m with
      | VLam (x, m) ->
        let n = eval env n in
        let env = VMap.add x n env in
        eval env m
      | VFix (x, b) ->
        let env = VMap.add x m env in
        eval env (App (b, n))
      | VSend ch ->
        let n = eval env n in
        let _ = sync (send ch n) in
        VCh ch
      | _ -> raise NonFunctionalApp)
    | Let (m, n) ->
      let x, un = unbind n in
      let m = eval env m in
      let env = VMap.add x m env in
      eval env un
    | Ind _ -> VBox
    | Constr (id, ms) ->
      let ms = List.map (eval env) ms in
      VConstr (id, ms)
    | Match (m, _, cls) -> (
      let m = eval env m in
      let opt =
        List.fold_left
          (fun opt cl ->
            match opt with
            | Some _ -> opt
            | None -> (
              try
                let p, ucl = unbind_p cl in
                let env = mk_env env p m in
                Some (eval env ucl)
              with
              | _ -> None))
          None cls
      in
      match opt with
      | Some m -> m
      | None -> raise UnMatchedPattern)
    | Fix m ->
      let x, um = unbind m in
      VFix (x, um)
    | Main -> VBox
    | Proto -> VBox
    | End -> VBox
    | Inp _ -> VBox
    | Out _ -> VBox
    | Ch _ -> VBox
    | Fork (_, m, n) ->
      let x, un = unbind n in
      let m = eval env m in
      let ch = new_channel () in
      let env = VMap.add x (VCh ch) env in
      let _ =
        create
          (fun env ->
            let _ = print_endline "hello from thread" in
            eval env un)
          env
      in
      VConstr (Id.pair_id, [ VCh ch; m ])
    | Send m -> (
      let m = eval env m in
      match m with
      | VCh ch -> VSend ch
      | _ -> raise NonChannelError)
    | Recv m -> (
      let m = eval env m in
      match m with
      | VCh ch ->
        let n = sync (receive ch) in
        VConstr (Id.pair_id, [ n; VCh ch ])
      | _ -> raise NonChannelError)
    | Close _ -> VConstr (Id.tt_id, [])
    | Axiom _ -> VBox
end
