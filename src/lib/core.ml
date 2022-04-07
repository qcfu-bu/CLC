open Format
open Bindlib
open Name

type sort =
  | U
  | L

let pp_v fmt x = fprintf fmt "%s" (name_of x)

module Term = struct
  type t =
    (* inference *)
    | Ann of t * t
    | Meta of Meta.t
    (* core *)
    | Knd of sort
    | Var of t var
    | Pi of sort * t * tbinder
    | Lam of sort * tbinder
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
      | Lam (t, b) ->
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
    | Pi (s, a, b) -> (
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
    | Lam (s, m) -> (
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

  let respine m sp = List.fold_left (fun acc m -> App (acc, m)) m sp

  let mk = new_var (fun x -> Var x)

  let blank = mk "_"

  let _U = box U

  let _L = box L

  let _Ann = box_apply2 (fun m a -> Ann (m, a))

  let _Meta x = box (Meta x)

  let _Knd s = box (Knd s)

  let _Var = box_var

  let _Pi s = box_apply2 (fun a b -> Pi (s, a, b))

  let _Lam s = box_apply (fun m -> Lam (s, m))

  let _mLam s xs m = List.fold_right (fun x acc -> _Lam s (bind_var x acc)) xs m

  let _App = box_apply2 (fun m n -> App (m, n))

  let _mApp m sp = List.fold_left (fun acc x -> _App acc x) m sp

  let _Let = box_apply2 (fun m n -> Let (m, n))

  let _Ind id = box_apply (fun ts -> Ind (id, ts))

  let _Constr id = box_apply (fun ts -> Constr (id, ts))

  let _Match = box_apply3 (fun m mot cls -> Match (m, mot, cls))

  let _Fix = box_apply (fun m -> Fix m)

  let _Main = box Main

  let _Proto = box Proto

  let _End = box End

  let _Inp = box_apply2 (fun a b -> Inp (a, b))

  let _Out = box_apply2 (fun a b -> Out (a, b))

  let _Ch = box_apply (fun m -> Ch m)

  let _Fork = box_apply3 (fun a m n -> Fork (a, m, n))

  let _Send = box_apply (fun m -> Send m)

  let _Recv = box_apply (fun m -> Recv m)

  let _Close = box_apply (fun m -> Close m)

  let _Axiom id = box_apply (fun m -> Axiom (id, m))

  let _Mot0 = box Mot0

  let _Mot1 = box_apply (fun mot -> Mot1 mot)

  let _Mot2 = box_apply (fun mot -> Mot2 mot)

  let _Mot3 = box_apply (fun mot -> Mot3 mot)

  let rec lift m =
    match m with
    | Ann (m, a) -> _Ann (lift m) (lift a)
    | Meta x -> _Meta x
    | Knd s -> _Knd s
    | Var x -> _Var x
    | Pi (s, a, b) -> _Pi s (lift a) (box_binder lift b)
    | Lam (s, m) -> _Lam s (box_binder lift m)
    | App (m, n) -> _App (lift m) (lift n)
    | Let (m, n) -> _Let (lift m) (box_binder lift n)
    | Ind (id, ms) ->
      let ms = List.map lift ms in
      _Ind id (box_list ms)
    | Constr (id, ms) ->
      let ms = List.map lift ms in
      _Constr id (box_list ms)
    | Match (m, mot, cls) -> (
      let m = lift m in
      let cls = box_list (List.map (box_binder_p lift) cls) in
      match mot with
      | Mot0 -> _Match m _Mot0 cls
      | Mot1 mot -> _Match m (_Mot1 (box_binder lift mot)) cls
      | Mot2 mot -> _Match m (_Mot2 (box_binder_p lift mot)) cls
      | Mot3 mot -> _Match m (_Mot3 (box_binder (box_binder_p lift) mot)) cls)
    | Fix m -> _Fix (box_binder lift m)
    | Main -> _Main
    | Proto -> _Proto
    | End -> _End
    | Inp (a, b) -> _Inp (lift a) (box_binder lift b)
    | Out (a, b) -> _Out (lift a) (box_binder lift b)
    | Ch m -> _Ch (lift m)
    | Fork (a, m, n) -> _Fork (lift a) (lift m) (box_binder lift n)
    | Send m -> _Send (lift m)
    | Recv m -> _Recv (lift m)
    | Close m -> _Close (lift m)
    | Axiom (id, m) -> _Axiom id (lift m)

  let rec eq_m eq mot1 mot2 =
    match (mot1, mot2) with
    | Mot0, Mot0 -> true
    | Mot1 mot1, Mot1 mot2 -> eq_binder eq mot1 mot2
    | Mot2 mot1, Mot2 mot2 -> eq_binder_p eq mot1 mot2
    | Mot3 mot1, Mot3 mot2 -> eq_binder (eq_binder_p eq) mot1 mot2
    | _ -> false

  let rec aeq m1 m2 =
    if m1 == m2 then
      true
    else
      match (m1, m2) with
      | Ann (m1, a1), Ann (m2, a2) -> aeq m1 m2 && aeq a1 a2
      | Meta x1, Meta x2 -> Meta.equal x1 x2
      | Knd s1, Knd s2 -> s1 = s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Pi (s1, a1, b1), Pi (s2, a2, b2) ->
        s1 = s2 && aeq a1 a2 && eq_binder aeq b1 b2
      | Lam (s1, m1), Lam (s2, m2) -> s1 = s2 && eq_binder aeq m1 m2
      | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
      | Let (m1, n1), Let (m2, n2) -> aeq m1 m2 && eq_binder aeq n1 n2
      | Ind (id1, ms1), Ind (id2, ms2) ->
        Id.equal id1 id2 && List.equal aeq ms1 ms2
      | Constr (id1, ms1), Constr (id2, ms2) ->
        Id.equal id1 id2 && List.equal aeq ms1 ms2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
        aeq m1 m2 && eq_m aeq mot1 mot2
        && List.equal (eq_binder_p aeq) cls1 cls2
      | Fix m1, Fix m2 -> eq_binder aeq m1 m2
      | Main, Main -> true
      | Proto, Proto -> true
      | End, End -> true
      | Inp (a1, b1), Inp (a2, b2) -> aeq a1 a2 && eq_binder aeq b1 b2
      | Out (a1, b1), Out (a2, b2) -> aeq a1 a2 && eq_binder aeq b1 b2
      | Ch m1, Ch m2 -> aeq m1 m2
      | Fork (a1, m1, n1), Fork (a2, m2, n2) ->
        aeq a1 a2 && aeq m1 m2 && eq_binder aeq n1 n2
      | Send m1, Send m2 -> aeq m1 m2
      | Recv m1, Recv m2 -> aeq m1 m2
      | Close m1, Close m2 -> aeq m1 m2
      | Axiom (id1, m1), Axiom (id2, m2) -> Id.equal id1 id2 && aeq m1 m2
      | _ -> false

  let rec whnf m =
    match m with
    | Ann (m, _) -> whnf m
    | App (m, n) -> (
      let m = whnf m in
      let n = whnf n in
      match m with
      | Lam (_, m) -> whnf (subst m n)
      | Fix b -> whnf (App (subst b m, n))
      | _ -> App (m, n))
    | Let (m, n) ->
      let m = whnf m in
      whnf (subst n m)
    | Match (m, mot, cls) -> (
      let m = whnf m in
      let opt =
        List.fold_left
          (fun opt cl ->
            match opt with
            | Some _ -> opt
            | None -> (
              try Some (subst_p cl m) with
              | _ -> None))
          None cls
      in
      match opt with
      | Some m -> whnf m
      | None -> Match (m, mot, cls))
    | _ -> m

  let rec equal m1 m2 =
    if aeq m1 m2 then
      true
    else
      let m1 = whnf m1 in
      let m2 = whnf m2 in
      match (m1, m2) with
      | Ann (m1, a1), Ann (m2, a2) -> equal m1 m2 && equal a1 a2
      | Meta x1, Meta x2 -> Meta.equal x1 x2
      | Knd s1, Knd s2 -> s1 = s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Pi (s1, a1, b1), Pi (s2, a2, b2) ->
        s1 = s2 && equal a1 a2 && eq_binder equal b1 b2
      | Lam (s1, m1), Lam (s2, m2) -> s1 = s2 && eq_binder equal m1 m2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (m1, n1), Let (m2, n2) -> equal m1 m2 && eq_binder equal n1 n2
      | Ind (id1, ms1), Ind (id2, ms2) ->
        Id.equal id1 id2 && List.equal equal ms1 ms2
      | Constr (id1, ms1), Constr (id2, ms2) ->
        Id.equal id1 id2 && List.equal equal ms1 ms2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
        equal m1 m2 && eq_m equal mot1 mot2
        && List.equal (eq_binder_p equal) cls1 cls2
      | Fix m1, Fix m2 -> eq_binder equal m1 m2
      | Main, Main -> true
      | Proto, Proto -> true
      | End, End -> true
      | Inp (a1, b1), Inp (a2, b2) -> equal a1 a2 && eq_binder equal b1 b2
      | Out (a1, b1), Out (a2, b2) -> equal a1 a2 && eq_binder equal b1 b2
      | Ch m1, Ch m2 -> equal m1 m2
      | Fork (a1, m1, n1), Fork (a2, m2, n2) ->
        equal a1 a2 && equal m1 m2 && eq_binder equal n1 n2
      | Send m1, Send m2 -> equal m1 m2
      | Recv m1, Recv m2 -> equal m1 m2
      | Close m1, Close m2 -> equal m1 m2
      | Axiom (id1, m1), Axiom (id2, m2) -> Id.equal id1 id2 && equal m1 m2
      | _ -> false
end

module Top = struct
  type ind = Ind of Id.t * pscope * constr list

  and constr = Constr of Id.t * pscope

  and pscope =
    | PBase of tscope
    | PBind of Term.t * psbinder

  and tscope =
    | TBase of Term.t
    | TBind of Term.t * tsbinder

  and psbinder = (Term.t, pscope) binder

  and tsbinder = (Term.t, tscope) binder

  type t =
    | Bottom
    | Define of Term.t * tbinder
    | Induct of ind * t
    | Import of Id.t * tbinder

  and tbinder = (Term.t, t) binder

  let rec pp fmt t =
    match t with
    | Bottom -> ()
    | Define (m, t) -> (
      match m with
      | Axiom (_, m) ->
        let x, ut = unbind t in
        fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" pp_v x Term.pp m pp ut
      | _ ->
        let x, ut = unbind t in
        fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" pp_v x Term.pp m pp
          ut)
    | Induct (Ind (id, a, cs), t) ->
      fprintf fmt "@[Inductive %a %a :=@.%a.@.@.%a@]" Id.pp id pp_pscope a
        pp_constr cs pp t
    | Import (_, t) ->
      let x, ut = unbind t in
      fprintf fmt "@[Import %a.@.@.%a@]" pp_v x pp ut

  and pp_constr fmt cs =
    match cs with
    | [] -> ()
    | Constr (id, a) :: cs ->
      fprintf fmt "@[<v 0>| %a %a@;<1 0>%a@]" Id.pp id pp_pscope a pp_constr cs

  and pp_pscope fmt a =
    match a with
    | PBase a -> pp_tscope fmt a
    | PBind (a, b) ->
      let x, ub = unbind b in
      if binder_occur b then
        fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x Term.pp a
          pp_pscope ub
      else
        fprintf fmt "@[(%a) ->@;<1 2>%a@]" Term.pp a pp_pscope ub

  and pp_tscope fmt a =
    match a with
    | TBase a -> Term.pp fmt a
    | TBind (a, b) ->
      let x, ub = unbind b in
      if binder_occur b then
        fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x Term.pp a
          pp_tscope ub
      else
        fprintf fmt "@[(%a) ->@;<1 2>%a@]" Term.pp a pp_tscope ub

  let _PBase = box_apply (fun a -> PBase a)

  let _PBind = box_apply2 (fun a b -> PBind (a, b))

  let _PBnd a b = _PBind a (bind_var Term.blank b)

  let _TBase = box_apply (fun m -> TBase m)

  let _TBind = box_apply2 (fun a b -> TBind (a, b))

  let _TBnd a b = _TBind a (bind_var Term.blank b)

  let _Ind id = box_apply2 (fun a cs -> Ind (id, a, cs))

  let _Constr id = box_apply (fun a -> Constr (id, a))

  let _Bottom = box Bottom

  let _Define = box_apply2 (fun m t -> Define (m, t))

  let _Induct = box_apply2 (fun ind t -> Induct (ind, t))

  let _Import id = box_apply (fun t -> Import (id, t))
end