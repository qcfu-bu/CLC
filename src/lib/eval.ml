open Format
open Bindlib
open Name
open Core
open Prelude
open Thread
open Event

module EvalTerm = struct
  open Term

  exception FunctionError of string

  exception MatchError

  exception SendError

  exception RecvError

  type ch =
    | Channel of value channel
    | Stdin
    | Stdout
    | Stderr

  and value =
    | VBox
    | VConstr of Id.t * value list
    | VLam of Term.v * Term.t
    | VFix of Term.v * Term.t
    | VCh of ch
    | VSend of ch

  type env = value VMap.t

  let rec pp fmt m =
    let rec aux fmt ms =
      match ms with
      | [] -> ()
      | [ m ] -> pp fmt m
      | m :: ms -> fprintf fmt "%a; %a" pp m aux ms
    in
    match m with
    | VBox -> fprintf fmt "VBox"
    | VConstr (id, ms) -> fprintf fmt "VConstr(%a, [%a])" Id.pp id aux ms
    | VLam (x, m) -> fprintf fmt "VLam(%a, %a)" pp_v x Term.pp m
    | VFix (x, m) -> fprintf fmt "VFix(%a, %a)" pp_v x Term.pp m
    | VCh ch -> fprintf fmt "VCh(%a)" pp_ch ch
    | VSend ch -> fprintf fmt "VSend(%a)" pp_ch ch

  and pp_ch fmt ch =
    match ch with
    | Channel ch -> fprintf fmt "<ch>"
    | Stdin -> fprintf fmt "stdin"
    | Stdout -> fprintf fmt "stdout"
    | Stderr -> fprintf fmt "stderr"

  let pair_id = Id.mk "pair"

  let rec mk_env env p m =
    match (p, m) with
    | PVar x, m -> VMap.add x m env
    | PInd _, _ -> raise PBacktrack
    | PConstr (id1, ps), VConstr (id2, ms) ->
      if Id.equal id1 id2 || Id.equal pair_id id2 then
        List.fold_left2 (fun acc p m -> mk_env acc p m) env ps ms
      else
        raise PBacktrack
    | _ -> raise PBacktrack

  let rec eval env m =
    match m with
    | Ann (m, _) -> eval env m
    | Meta _ -> VBox
    | Struct (_, ms) ->
      let ms = List.map (eval env) ms in
      VConstr (pair_id, ms)
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
      | VSend m -> (
        let n = eval env n in
        match m with
        | Channel ch ->
          let _ = sync (send ch n) in
          VCh m
        | Stdout ->
          (* TODO: convert string output *)
          let _ = printf "%a\n" pp n in
          VCh m
        | Stderr ->
          (* TODO: convert string output *)
          let s = asprintf "%a\n" pp n in
          let _ = prerr_endline s in
          VCh m
        | _ -> raise SendError)
      | _ -> raise (FunctionError (asprintf "non-functional:=@.%a" pp m)))
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
      | None -> raise MatchError)
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
      let ch = VCh (Channel (new_channel ())) in
      let env = VMap.add x ch env in
      let t_id = id (self ()) in
      let _ = printf "forking from thread(%d)\n" t_id in
      let _ =
        create
          (fun env ->
            let t_id = id (self ()) in
            let _ = printf "hello from thread(%d)\n" t_id in
            eval env un)
          env
      in
      VConstr (pair_id, [ ch; m ])
    | Send m -> (
      let m = eval env m in
      match m with
      | VCh ch -> VSend ch
      | _ -> raise SendError)
    | Recv m -> (
      let m = eval env m in
      match m with
      | VCh (Channel ch) ->
        let n = sync (receive ch) in
        VConstr (pair_id, [ n; m ])
      | VCh Stdin ->
        (* TODO: convert string input *)
        let s = read_line () in
        let _ = print_endline s in
        VConstr (pair_id, [ VBox; m ])
      | _ -> raise RecvError)
    | Close _ -> VConstr (Prelude.tt_id, [])
    | Axiom _ -> VBox
end

module EvalTop = struct
  open Term
  open Top
  open EvalTerm

  exception ImportError

  let eval t =
    let env = VMap.singleton Prelude.main_v VBox in
    let rec aux env t =
      match t with
      | Main m -> EvalTerm.eval env m
      | Define (m, t) ->
        let x, ut = unbind t in
        let m = EvalTerm.eval env m in
        let env = VMap.add x m env in
        aux env ut
      | Induct (_, t) -> aux env t
      | Import (id, _, t) ->
        let x, ut = unbind t in
        if Id.equal Id.stdin_id id then
          let env = VMap.add x (VCh Stdin) env in
          aux env ut
        else if Id.equal Id.stdout_id id then
          let env = VMap.add x (VCh Stdout) env in
          aux env ut
        else if Id.equal Id.stderr_id id then
          let env = VMap.add x (VCh Stderr) env in
          aux env ut
        else
          raise ImportError
    in
    aux env t
end
