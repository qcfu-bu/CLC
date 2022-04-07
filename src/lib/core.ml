open Format
open Bindlib
open Name

type sort =
  | U
  | L

module Term = struct
  type t =
    (* inference *)
    | Ann of t * t
    | Meta of Meta.t
    (* core *)
    | Knd of sort
    | Var of t var
    | Pi of t * tbinder * sort
    | Lam of tbinder * sort
    | App of t * t
    | Let of t * tbinder
    (* inductive *)
    | Ind of Id.t * t list
    | Constr of Id.t * t list
    | Match of t * m * pbinder list
    | Fix of tbinder
    (* session *)
    | Main
    | Proto
    | End
    | Inp of t * tbinder
    | Out of t * tbinder
    | Ch of t
    | Fork of t * t * tbinder
    | Send of t
    | Recv of t
    | Close of t
    (* magic *)
    | Axiom of Id.t * t

  and p =
    | PVar of t var
    | PInd of Id.t * p list
    | PConstr of Id.t * p list

  and p0 =
    | P0Rel
    | P0Ind of Id.t * p0 list
    | P0Constr of Id.t * p0 list

  and m =
    | Mot0
    | Mot1 of tbinder
    | Mot2 of pbinder
    | Mot3 of tpbinder

  and tbinder = (t, t) binder

  and pbinder = p0 * (t, t) mbinder

  and tpbinder = (t, pbinder) binder

  exception PBacktrack

  let rec equal_p0 p1 p2 =
    match (p1, p2) with
    | P0Rel, P0Rel -> true
    | P0Ind (id1, ps1), P0Ind (id2, ps2) -> (
      try
        Id.equal id1 id2
        && List.fold_left2 (fun acc p1 p2 -> acc && equal_p0 p1 p2) true ps1 ps2
      with
      | _ -> false)
    | P0Constr (id1, ps1), P0Constr (id2, ps2) -> (
      try
        Id.equal id1 id2
        && List.fold_left2 (fun acc p1 p2 -> acc && equal_p0 p1 p2) true ps1 ps2
      with
      | _ -> false)
    | _ -> false

  and pp_p0 fmt p =
    match p with
    | P0Rel -> fprintf fmt "P0Rel"
    | P0Ind (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps0 ps
    | P0Constr (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps0 ps

  and pp_ps0 fmt = function
    | [ p ] -> fprintf fmt "%a" pp_p0 p
    | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p0 p pp_ps0 ps
    | _ -> ()

  and mt_of_pt0 p0 t =
    match (p0, t) with
    | P0Rel, _ -> [| t |]
    | P0Ind (id1, ps), Ind (id2, ts) ->
      if Id.equal id1 id2 then
        List.fold_left2
          (fun acc p t -> Array.append acc (mt_of_pt0 p t))
          [||] ps ts
      else
        raise PBacktrack
    | P0Constr (id1, ps), Constr (id2, ts) ->
      if Id.equal id1 id2 then
        List.fold_left2
          (fun acc p t -> Array.append acc (mt_of_pt0 p t))
          [||] ps ts
      else
        raise PBacktrack
    | _ -> raise PBacktrack

  and mvar_of_p p =
    match p with
    | PVar x -> (P0Rel, [| x |])
    | PInd (id, ps) ->
      let ps0, m =
        List.fold_left
          (fun (ps0, acc) p ->
            let p0, m = mvar_of_p p in
            (p0 :: ps0, Array.append acc m))
          ([], [||])
          ps
      in
      (P0Ind (id, List.rev ps0), m)
    | PConstr (id, ps) ->
      let ps0, m =
        List.fold_left
          (fun (ps0, acc) p ->
            let p0, m = mvar_of_p p in
            (p0 :: ps0, Array.append acc m))
          ([], [||])
          ps
      in
      (P0Constr (id, List.rev ps0), m)

  and list_of_p p =
    match p with
    | PVar x -> [ x ]
    | PInd (_, ps) ->
      let xss = List.fold_right (fun p acc -> list_of_p p :: acc) ps [] in
      List.concat xss
    | PConstr (_, ps) ->
      let xss = List.fold_right (fun p acc -> list_of_p p :: acc) ps [] in
      List.concat xss

  and p_of_mvar p0 m =
    match p0 with
    | P0Rel ->
      let x = m.(0) in
      let m = Array.sub m 1 (Array.length m - 1) in
      (PVar x, m)
    | P0Ind (id, ps) ->
      let ps, m =
        List.fold_left
          (fun (ps, m) p0 ->
            let p, m = p_of_mvar p0 m in
            (p :: ps, m))
          ([], m) ps
      in
      (PInd (id, List.rev ps), m)
    | P0Constr (id, ps) ->
      let ps, m =
        List.fold_left
          (fun (ps, m) p0 ->
            let p, m = p_of_mvar p0 m in
            (p :: ps, m))
          ([], m) ps
      in
      (PConstr (id, List.rev ps), m)

  and bind_p p tb =
    let p0, m = mvar_of_p p in
    let mb = bind_mvar m tb in
    box_apply (fun mb -> (p0, mb)) mb

  and unbind_p pb =
    let p0, mb = pb in
    let m, t = unmbind mb in
    let p, _ = p_of_mvar p0 m in
    (p, t)

  and unbind_p2 pb1 pb2 =
    let p1, mb1 = pb1 in
    let p2, mb2 = pb2 in
    assert (equal_p0 p1 p2);
    let m, t1, t2 = unmbind2 mb1 mb2 in
    let p, _ = p_of_mvar p1 m in
    (p, t1, t2)

  and subst_p pb t =
    let p0, mb = pb in
    let m = mt_of_pt0 p0 t in
    let t = msubst mb m in
    t

  and box_binder_p f pb =
    let p0, mb = pb in
    let mb = box_mbinder f mb in
    box_apply (fun mb -> (p0, mb)) mb

  and eq_binder_p f pb1 pb2 =
    let p1, mb1 = pb1 in
    let p2, mb2 = pb2 in
    equal_p0 p1 p2 && eq_mbinder f mb1 mb2

  let pp_v fmt x = fprintf fmt "%s" (name_of x)

  let rec pp_p fmt p =
    match p with
    | PVar x -> pp_v fmt x
    | PInd (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps
    | PConstr (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps

  and pp_ps fmt ps =
    match ps with
    | [ p ] -> pp_p fmt p
    | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p p pp_ps ps
    | _ -> ()

  let rec pp fmt m =
    let rec spine s m =
      match m with
      | Lam (b, t) ->
        if s = t then
          let x, m = unbind b in
          let xs, m = spine s m in
          (x :: xs, m)
        else
          ([], m)
      | _ -> ([], m)
    in
    match m with
    | Ann (m, a) -> fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp m pp a
    | Meta x -> Meta.pp fmt x
    | Knd s -> (
      match s with
      | U -> fprintf fmt "U"
      | L -> fprintf fmt "L")
    | Var x -> pp_v fmt x
    | Pi (a, b, s) -> (
      let x, ub = unbind b in
      match s with
      | U ->
        if binder_occur b then
          fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x pp a pp
            ub
        else
          fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp a pp ub
      | L ->
        if binder_occur b then
          fprintf fmt "@[@[linear (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x pp a pp
            ub
        else
          fprintf fmt "@[(%a) -o@;<1 2>%a@]" pp a pp ub)
    | Lam (m, s) -> (
      let x, um = unbind m in
      let xs, um = spine s um in
      match s with
      | U -> fprintf fmt "@[fun %a %a =>@;<1 2>%a@]" pp_v x pp_vs xs pp um
      | L -> fprintf fmt "@[lin %a %a =>@;<1 2>%a@]" pp_v x pp_vs xs pp um)
    | App (m, n) -> fprintf fmt "@[(%a)@;<1 2>%a@]" pp m pp n
    | Let (m, n) ->
      let x, un = unbind n in
      fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" pp_v x pp m pp
        un
    | Ind (id, ms) -> (
      match ms with
      | [] -> Id.pp fmt id
      | _ -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms)
    | Constr (id, ms) -> (
      match ms with
      | [] -> Id.pp fmt id
      | _ -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms)
    | Match (m, mot, cls) ->
      fprintf fmt "@[<v 0>@[match %a%a@;<1 0>with@]@;<1 0>@[%a@]end@]" pp m pp_m
        mot pp_cls cls
    | Fix m ->
      let x, um = unbind m in
      let xs, um = spine U um in
      fprintf fmt "@[fix %a %a =>@;<1 2>%a@]" pp_v x pp_vs xs pp um
    | Main -> fprintf fmt "main"
    | Proto -> fprintf fmt "proto"
    | End -> fprintf fmt "$"
    | Inp (a, b) ->
      let x, ub = unbind b in
      fprintf fmt "@[?(%a : %a),@;<1 2>%a@]" pp_v x pp a pp ub
    | Out (a, b) ->
      let x, ub = unbind b in
      fprintf fmt "@[!(%a : %a),@;<1 2>%a@]" pp_v x pp a pp ub
    | Ch m -> fprintf fmt "ch %a" pp m
    | Fork (a, m, n) ->
      let x, un = unbind n in
      fprintf fmt "@[@[fork (%a :@;<1 2>%a) :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
        pp_v x pp a pp m pp un
    | Send m -> fprintf fmt "send %a" pp m
    | Recv m -> fprintf fmt "recv %a" pp m
    | Close m -> fprintf fmt "close %a" pp m
    | Axiom (id, _) -> Id.pp fmt id

  and pp_vs fmt xs =
    match xs with
    | [] -> ()
    | [ x ] -> pp_v fmt x
    | x :: xs -> fprintf fmt "%a %a" pp_v x pp_vs xs

  and pp_ts fmt ms =
    match ms with
    | [ m ] -> pp fmt m
    | m :: ms -> fprintf fmt "@[%a@;<1 2>%a@]" pp m pp_ts ms
    | _ -> ()

  and pp_m fmt mot =
    match mot with
    | Mot0 -> ()
    | Mot1 mot ->
      let x, umot = unbind mot in
      fprintf fmt "as %a return@;<1 2>%a" pp_v x pp umot
    | Mot2 mot ->
      let p, umot = unbind_p mot in
      fprintf fmt "in %a return@;<1 2>%a" pp_p p pp umot
    | Mot3 mot ->
      let x, mot = unbind mot in
      let p, umot = unbind_p mot in
      fprintf fmt "as %a in %a return@;<1 2>%a" pp_v x pp_p p pp umot

  and pp_cl fmt cl =
    let p, ucl = unbind_p cl in
    fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp ucl

  and pp_cls fmt cls =
    match cls with
    | [] -> ()
    | cl :: cls -> fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls

  let spine m =
    let rec aux m sp =
      match m with
      | App (m, n) -> aux m (n :: sp)
      | _ -> (m, sp)
    in
    aux m []

  let mk = new_var (fun x -> Var x)

  let blank = mk "_"

  let _Var = box_var

  let _Meta x = box (Meta x)
end