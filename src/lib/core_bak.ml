open Format
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
    | Var of Var.t
    | Pi of Var.t * t * t * sort
    | Lam of Var.t * t * sort
    | App of t * t
    | Let of Var.t * t * t
    (* inductive *)
    | Ind of Id.t * t list
    | Constr of Id.t * t list
    | Match of t * m * (p * t) list
    | Fix of Var.t * t
    (* session *)
    | Main
    | Proto
    | End
    | Inp of Var.t * t * t
    | Out of Var.t * t * t
    | Ch of t
    | Fork of Var.t * t * t * t
    | Send of t
    | Recv of t
    | Close of t
    (* magic *)
    | Axiom of Id.t * t

  and p =
    | PInd of Id.t * Var.t list
    | PConstr of Id.t * Var.t list

  and m =
    | Mot0
    | Mot1 of Var.t * t
    | Mot2 of p * t
    | Mot3 of Var.t * p * t

  let rec occurs x tm =
    match tm with
    | Ann (m, a) -> occurs x m || occurs x a
    | Meta _ -> false
    | Knd _ -> false
    | Var y -> Var.equal x y
    | Pi (_, a, b, _) -> occurs x a || occurs (Var.incr 1 x) b
    | Lam (_, m, _) -> occurs (Var.incr 1 x) m
    | App (m, n) -> occurs x m || occurs x n
    | Let (_, m, n) -> occurs x m || occurs (Var.incr 1 x) n
    | Ind (_, ms) -> List.exists (occurs x) ms
    | Constr (_, ms) -> List.exists (occurs x) ms
    | Match (m, mot, cls) -> (
      occurs x m
      || List.exists
           (fun (p, bod) ->
             match p with
             | PInd (_, xs) ->
               let n = List.length xs in
               occurs (Var.incr n x) bod
             | PConstr (_, xs) ->
               let n = List.length xs in
               occurs (Var.incr n x) bod)
           cls
      ||
      match mot with
      | Mot0 -> true
      | Mot1 (_, mot) -> occurs (Var.incr 1 x) mot
      | Mot2 (p, mot) -> (
        match p with
        | PInd (_, xs) ->
          let n = List.length xs in
          occurs (Var.incr n x) mot
        | PConstr (_, xs) ->
          let n = List.length xs in
          occurs (Var.incr n x) mot)
      | Mot3 (_, p, mot) -> (
        match p with
        | PInd (_, xs) ->
          let n = List.length xs in
          occurs (Var.incr (n + 1) x) mot
        | PConstr (_, xs) ->
          let n = List.length xs in
          occurs (Var.incr (n + 1) x) mot))
    | Fix (_, m) -> occurs (Var.incr 1 x) m
    | Main -> false
    | Proto -> false
    | End -> false
    | Inp (_, a, b) -> occurs x a || occurs (Var.incr 1 x) b
    | Out (_, a, b) -> occurs x a || occurs (Var.incr 1 x) b
    | Ch m -> occurs x m
    | Fork (_, a, m, n) -> occurs x a || occurs x m || occurs (Var.incr 1 x) n
    | Send m -> occurs x m
    | Recv m -> occurs x m
    | Close m -> occurs x m
    | Axiom (_, m) -> occurs x m

  let upren f x = Var.case x (fun x -> x) (fun x -> Var.incr 1 (f x))

  let rec upren_n n f =
    if n <= 0 then
      f
    else
      upren_n (n - 1) (upren f)

  let rec ren f tm =
    match tm with
    | Ann (m, a) ->
      let m = ren f m in
      let a = ren f a in
      Ann (m, a)
    | Meta _ -> tm
    | Knd _ -> tm
    | Var x -> Var (f x)
    | Pi (x, a, b, s) ->
      let a = ren f a in
      let b = ren (upren f) b in
      Pi (x, a, b, s)
    | Lam (x, m, s) ->
      let m = ren f m in
      Lam (x, m, s)
    | App (m, n) ->
      let m = ren f m in
      let n = ren f n in
      App (m, n)
    | Let (x, m, n) ->
      let m = ren f m in
      let n = ren (upren f) n in
      Let (x, m, n)
    | Ind (id, ms) ->
      let ms = List.map (ren f) ms in
      Ind (id, ms)
    | Constr (id, ms) ->
      let ms = List.map (ren f) ms in
      Constr (id, ms)
    | Match (m, mot, cls) -> (
      let m = ren f m in
      let cls =
        List.map
          (fun (p, bod) ->
            match p with
            | PInd (_, xs) ->
              let n = List.length xs in
              let bod = ren (upren_n n f) bod in
              (p, bod)
            | PConstr (_, xs) ->
              let n = List.length xs in
              let bod = ren (upren_n n f) bod in
              (p, bod))
          cls
      in
      match mot with
      | Mot0 -> Match (m, Mot0, cls)
      | Mot1 (x, mot) ->
        let mot = ren (upren f) mot in
        Match (m, Mot1 (x, mot), cls)
      | Mot2 (p, mot) -> (
        match p with
        | PInd (_, xs) ->
          let n = List.length xs in
          let mot = ren (upren_n n f) mot in
          Match (m, Mot2 (p, mot), cls)
        | PConstr (_, xs) ->
          let n = List.length xs in
          let mot = ren (upren_n n f) mot in
          Match (m, Mot2 (p, mot), cls))
      | Mot3 (x, p, mot) -> (
        match p with
        | PInd (_, xs) ->
          let n = List.length xs in
          let mot = ren (upren_n (n + 1) f) mot in
          Match (m, Mot3 (x, p, mot), cls)
        | PConstr (_, xs) ->
          let n = List.length xs in
          let mot = ren (upren_n (n + 1) f) mot in
          Match (m, Mot3 (x, p, mot), cls)))
    | Fix (x, m) ->
      let m = ren (upren f) m in
      Fix (x, m)
    | Main -> tm
    | Proto -> tm
    | End -> tm
    | Inp (x, a, b) ->
      let a = ren f a in
      let b = ren (upren f) b in
      Inp (x, a, b)
    | Out (x, a, b) ->
      let a = ren f a in
      let b = ren (upren f) b in
      Out (x, a, b)
    | Ch m ->
      let m = ren f m in
      Ch m
    | Fork (x, a, m, n) ->
      let a = ren f a in
      let m = ren f m in
      let n = ren (upren f) n in
      Fork (x, a, m, n)
    | Send m ->
      let m = ren f m in
      Send m
    | Recv m ->
      let m = ren f m in
      Recv m
    | Close m ->
      let m = ren f m in
      Close m
    | Axiom (id, m) ->
      let m = ren f m in
      Axiom (id, m)

  let up f x = Var.case x (fun x -> Var x) (fun x -> ren (Var.incr 1) (f x))

  let rec upn n f =
    if n <= 0 then
      f
    else
      upn (n - 1) (up f)

  let rec fsubst f tm =
    match tm with
    | Ann (m, a) ->
      let m = fsubst f m in
      let a = fsubst f a in
      Ann (m, a)
    | Meta _ -> tm
    | Knd _ -> tm
    | Var x -> f x
    | Pi (x, a, b, s) ->
      let a = fsubst f a in
      let b = fsubst (up f) b in
      Pi (x, a, b, s)
    | Lam (x, m, s) ->
      let m = fsubst (up f) m in
      Lam (x, m, s)
    | App (m, n) ->
      let m = fsubst f m in
      let n = fsubst f n in
      App (m, n)
    | Let (x, m, n) ->
      let m = fsubst f m in
      let n = fsubst (up f) n in
      Let (x, m, n)
    | Ind (id, ms) ->
      let ms = List.map (fsubst f) ms in
      Ind (id, ms)
    | Constr (id, ms) ->
      let ms = List.map (fsubst f) ms in
      Constr (id, ms)
    | Match (m, mot, cls) -> (
      let m = fsubst f m in
      let cls =
        List.map
          (fun (p, bod) ->
            match p with
            | PInd (_, xs) ->
              let n = List.length xs in
              let bod = fsubst (upn n f) bod in
              (p, bod)
            | PConstr (_, xs) ->
              let n = List.length xs in
              let bod = fsubst (upn n f) bod in
              (p, bod))
          cls
      in
      match mot with
      | Mot0 -> Match (m, Mot0, cls)
      | Mot1 (x, mot) ->
        let mot = fsubst (up f) mot in
        Match (m, Mot1 (x, mot), cls)
      | Mot2 (p, mot) -> (
        match p with
        | PInd (_, xs) ->
          let n = List.length xs in
          let mot = fsubst (upn n f) mot in
          Match (m, Mot2 (p, mot), cls)
        | PConstr (_, xs) ->
          let n = List.length xs in
          let mot = fsubst (upn n f) mot in
          Match (m, Mot2 (p, mot), cls))
      | Mot3 (_, p, mot) -> (
        match p with
        | PInd (_, xs) ->
          let n = List.length xs in
          let mot = fsubst (upn (n + 1) f) mot in
          Match (m, Mot2 (p, mot), cls)
        | PConstr (_, xs) ->
          let n = List.length xs in
          let mot = fsubst (upn (n + 1) f) mot in
          Match (m, Mot2 (p, mot), cls)))
    | Fix (x, m) ->
      let m = fsubst (up f) m in
      Fix (x, m)
    | Main -> tm
    | Proto -> tm
    | End -> tm
    | Inp (x, a, b) ->
      let a = fsubst f a in
      let b = fsubst (up f) b in
      Inp (x, a, b)
    | Out (x, a, b) ->
      let a = fsubst f a in
      let b = fsubst (up f) b in
      Out (x, a, b)
    | Ch m ->
      let m = fsubst f m in
      Ch m
    | Fork (x, a, m, n) ->
      let a = fsubst f a in
      let m = fsubst f m in
      let n = fsubst (up f) n in
      Fork (x, a, m, n)
    | Send m ->
      let m = fsubst f m in
      Send m
    | Recv m ->
      let m = fsubst f m in
      Recv m
    | Close m ->
      let m = fsubst f m in
      Close m
    | Axiom (id, m) ->
      let m = fsubst f m in
      Axiom (id, m)

  let scons m f x = Var.case x (fun _ -> m) (fun x -> f x)

  let subst m n = fsubst (scons m (fun x -> Var x)) n

  let substn ms n =
    let f = List.fold_right (fun m acc -> scons m acc) ms (fun x -> Var x) in
    fsubst f n

  let rec whnf tm =
    match tm with
    | Ann (m, _) -> whnf m
    | Meta _ -> tm
    | Knd _ -> tm
    | Var _ -> tm
    | Pi _ -> tm
    | Lam _ -> tm
    | App (m, n) -> (
      let m = whnf m in
      match m with
      | Lam (_, bod, _) -> whnf (subst n bod)
      | Fix (_, bod) -> whnf (App (subst m bod, n))
      | _ -> App (m, n))
    | Let (_, m, n) ->
      let m = whnf m in
      whnf (subst m n)
    | Ind _ -> tm
    | Constr _ -> tm
    | Match (m, mot, cls) -> (
      let m = whnf m in
      match m with
      | Constr (id1, ms) -> (
        let opt =
          List.fold_left
            (fun opt (p, bod) ->
              match (opt, p) with
              | None, PConstr (id2, _) ->
                if Id.equal id1 id2 then
                  Some (substn ms bod)
                else
                  None
              | _ -> opt)
            None cls
        in
        match opt with
        | Some m -> whnf m
        | None -> Match (m, mot, cls))
      | _ -> Match (m, mot, cls))
    | Fix _ -> tm
    | Main -> tm
    | Proto -> tm
    | End -> tm
    | Inp _ -> tm
    | Out _ -> tm
    | Ch _ -> tm
    | Fork _ -> tm
    | Send _ -> tm
    | Recv _ -> tm
    | Close _ -> tm
    | Axiom _ -> tm

  let rec equal t1 t2 =
    if t1 = t2 then
      true
    else
      let t1 = whnf t1 in
      let t2 = whnf t2 in
      match (t1, t2) with
      | Ann (m1, a1), Ann (m2, a2) -> equal m1 m2 && equal a1 a2
      | Meta x1, Meta x2 -> Meta.equal x1 x2
      | Knd s1, Knd s2 -> s1 = s2
      | Var x1, Var x2 -> Var.equal x1 x2
      | Pi (_, a1, b1, s1), Pi (_, a2, b2, s2) ->
        equal a1 a2 && equal b1 b2 && s1 = s2
      | Lam (_, m1, s1), Lam (_, m2, s2) -> equal m1 m2 && s1 = s2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (_, m1, n1), Let (_, m2, n2) -> equal m1 m2 && equal n1 n2
      | Ind (id1, ms1), Ind (id2, ms2) ->
        Id.equal id1 id2 && List.equal equal ms1 ms2
      | Constr (id1, ms1), Constr (id2, ms2) ->
        Id.equal id1 id2 && List.equal equal ms1 ms2
      | Match (m1, mot1, cls1), Match (m2, mot2, cls2) -> (
        equal m1 m2
        && List.equal
             (fun (p1, bod1) (p2, bod2) ->
               match (p1, p2) with
               | PInd (id1, _), PInd (id2, _) ->
                 Id.equal id1 id2 && equal bod1 bod2
               | PConstr (id1, _), PConstr (id2, _) ->
                 Id.equal id1 id2 && equal bod1 bod2
               | _ -> false)
             cls1 cls2
        &&
        match (mot1, mot2) with
        | Mot0, Mot0 -> true
        | Mot1 (_, mot1), Mot1 (_, mot2) -> equal mot1 mot2
        | Mot2 (p1, mot1), Mot2 (p2, mot2) -> (
          match (p1, p2) with
          | PInd (id1, _), PInd (id2, _) -> Id.equal id1 id2 && equal mot1 mot2
          | PConstr (id1, _), PConstr (id2, _) ->
            Id.equal id1 id2 && equal mot1 mot2
          | _ -> false)
        | Mot3 (_, p1, mot1), Mot3 (_, p2, mot2) -> (
          match (p1, p2) with
          | PInd (id1, _), PInd (id2, _) -> Id.equal id1 id2 && equal mot1 mot2
          | PConstr (id1, _), PConstr (id2, _) ->
            Id.equal id1 id2 && equal mot1 mot2
          | _ -> false)
        | _ -> false)
      | Fix (_, m1), Fix (_, m2) -> equal m1 m2
      | Main, Main -> true
      | Proto, Proto -> true
      | End, End -> true
      | Inp (_, a1, b1), Inp (_, a2, b2) -> equal a1 a2 && equal b1 b2
      | Out (_, a1, b1), Out (_, a2, b2) -> equal a1 a2 && equal b1 b2
      | Ch m1, Ch m2 -> equal m1 m2
      | Fork (_, a1, m1, n1), Fork (_, a2, m2, n2) ->
        equal a1 a2 && equal m1 m2 && equal n1 n2
      | Send m1, Send m2 -> equal m1 m2
      | Recv m1, Recv m2 -> equal m1 m2
      | Close m1, Close m2 -> equal m1 m2
      | Axiom (id1, m1), Axiom (id2, m2) -> Id.equal id1 id2 && equal m1 m2
      | _ -> false

  let pp_sort fmt s =
    match s with
    | U -> fprintf fmt "U"
    | L -> fprintf fmt "L"

  let rec pp fmt tm =
    let rec spine s tm =
      match tm with
      | Lam (x, m, t) ->
        if s = t then
          let xs, tm = spine s m in
          (x :: xs, tm)
        else
          ([], tm)
      | _ -> ([], tm)
    in
    match tm with
    | Ann (m, a) -> fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp m pp a
    | Meta x -> Meta.pp fmt x
    | Knd s -> pp_sort fmt s
    | Var x -> Var.pp fmt x
    | Pi (x, a, b, s) -> (
      match s with
      | U ->
        if occurs x b then
          fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" Var.pp x pp a
            pp b
        else
          fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp a pp b
      | L ->
        if occurs x b then
          fprintf fmt "@[@[linear (%a :@;<1 2>%a),@]@;<1 2>%a@]" Var.pp x pp a
            pp b
        else
          fprintf fmt "@[(%a) -o@;<1 2>%a@]" pp a pp b)
    | Lam (x, m, s) -> (
      let xs, m = spine s m in
      match s with
      | U -> fprintf fmt "@[fun %a %a =>@;<1 2>%a@]" Var.pp x pp_xs xs pp m
      | L -> fprintf fmt "@[lin %a %a =>@;<1 2>%a@]" Var.pp x pp_xs xs pp m)
    | App (m, n) -> fprintf fmt "@[(%a)@;<1 2>%a@]" pp m pp n
    | Let (x, m, n) ->
      fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" Var.pp x pp m
        pp n
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
    | Fix (x, m) ->
      let xs, m = spine U m in
      fprintf fmt "@[fix %a %a =>@;<1 2>%a@]" Var.pp x pp_xs xs pp m
    | Main -> fprintf fmt "main"
    | Proto -> fprintf fmt "proto"
    | End -> fprintf fmt "$"
    | Inp (x, a, b) -> fprintf fmt "@[?(%a : %a),@;<1 2>%a@]" Var.pp x pp a pp b
    | Out (x, a, b) -> fprintf fmt "@[!(%a : %a),@;<1 2>%a@]" Var.pp x pp a pp b
    | Ch m -> fprintf fmt "ch %a" pp m
    | Fork (x, a, m, n) ->
      fprintf fmt "@[@[fork (%a :@;<1 2>%a) :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
        Var.pp x pp a pp m pp n
    | Send m -> fprintf fmt "send %a" pp m
    | Recv m -> fprintf fmt "recv %a" pp m
    | Close m -> fprintf fmt "close %a" pp m
    | Axiom (id, _) -> Id.pp fmt id

  and pp_xs fmt xs =
    match xs with
    | [] -> ()
    | [ x ] -> Var.pp fmt x
    | x :: xs -> fprintf fmt "%a %a" Var.pp x pp_xs xs

  and pp_ts fmt ts =
    match ts with
    | [ t ] -> pp fmt t
    | t :: ts -> fprintf fmt "@[%a@;<1 2>%a@]" pp t pp_ts ts
    | _ -> ()

  and pp_p fmt p =
    match p with
    | PInd (id, xs) -> fprintf fmt "%a %a" Id.pp id pp_xs xs
    | PConstr (id, xs) -> fprintf fmt "%a %a" Id.pp id pp_xs xs

  and pp_m fmt m =
    match m with
    | Mot0 -> ()
    | Mot1 (x, mot) -> fprintf fmt "as %a return@;<1 2>%a" Var.pp x pp mot
    | Mot2 (p, mot) -> fprintf fmt "in %a return@;<1 2>%a" pp_p p pp mot
    | Mot3 (x, p, mot) ->
      fprintf fmt "as %a in %a return@;<1 2>%a" Var.pp x pp_p p pp mot

  and pp_cl fmt (p, bod) = fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp bod

  and pp_cls fmt cls =
    match cls with
    | [] -> ()
    | cl :: cls -> fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls
end

module Top = struct
  open Term

  type ind = Id.t * pscope * constr list

  and constr = Id.t * pscope

  and pscope =
    | PBase of tscope
    | PScope of Var.t * Term.t * pscope

  and tscope =
    | TBase of Term.t
    | TScope of Var.t * Term.t * tscope

  type t =
    | Bottom
    | Define of Var.t * Term.t * t
    | Induct of ind * t
    | Import of Id.t * t

  let rec ren f tp =
    match tp with
    | Bottom -> tp
    | Define (x, m, tp) ->
      let m = Term.ren f m in
      let tp = ren (upren f) tp in
      Define (x, m, tp)
    | Induct (ind, tp) ->
      let ind = ren_ind f ind in
      let tp = ren f tp in
      Induct (ind, tp)
    | Import (id, tp) ->
      let tp = ren (upren f) tp in
      Import (id, tp)

  and ren_ind f (id, a, cs) =
    let a = ren_pscope f a in
    let cs = List.map (ren_constr f) cs in
    (id, a, cs)

  and ren_constr f (id, a) =
    let a = ren_pscope f a in
    (id, a)

  and ren_pscope f a =
    match a with
    | PBase a ->
      let a = ren_tscope f a in
      PBase a
    | PScope (x, a, b) ->
      let a = Term.ren f a in
      let b = ren_pscope (upren f) b in
      PScope (x, a, b)

  and ren_tscope f a =
    match a with
    | TBase a ->
      let a = Term.ren f a in
      TBase a
    | TScope (x, a, b) ->
      let a = Term.ren f a in
      let b = ren_tscope (upren f) b in
      TScope (x, a, b)

  let rec fsubst f tp =
    match tp with
    | Bottom -> tp
    | Define (x, m, tp) ->
      let m = Term.fsubst f m in
      let tp = fsubst (up f) tp in
      Define (x, m, tp)
    | Induct (ind, tp) ->
      let ind = fsubst_ind f ind in
      let tp = fsubst f tp in
      Induct (ind, tp)
    | Import (id, tp) ->
      let tp = fsubst (up f) tp in
      Import (id, tp)

  and fsubst_ind f (id, a, cs) =
    let a = fsubst_pscope f a in
    let cs = List.map (fsubst_constr f) cs in
    (id, a, cs)

  and fsubst_constr f (id, a) =
    let a = fsubst_pscope f a in
    (id, a)

  and fsubst_pscope f a =
    match a with
    | PBase a ->
      let a = fsubst_tscope f a in
      PBase a
    | PScope (x, a, b) ->
      let a = Term.fsubst f a in
      let b = fsubst_pscope (up f) b in
      PScope (x, a, b)

  and fsubst_tscope f a =
    match a with
    | TBase a ->
      let a = Term.fsubst f a in
      TBase a
    | TScope (x, a, b) ->
      let a = Term.fsubst f a in
      let b = fsubst_tscope (up f) b in
      TScope (x, a, b)

  let rec occurs_pscope x a =
    match a with
    | PBase a -> occurs_tscope x a
    | PScope (_, a, b) -> Term.occurs x a || occurs_pscope (Var.incr 1 x) b

  and occurs_tscope x a =
    match a with
    | TBase a -> Term.occurs x a
    | TScope (_, a, b) -> Term.occurs x a || occurs_tscope (Var.incr 1 x) b

  let rec pp fmt tp =
    match tp with
    | Bottom -> ()
    | Define (x, m, tp) -> (
      match m with
      | Axiom (_, a) ->
        fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" Var.pp x Term.pp a pp tp
      | _ ->
        fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" Var.pp x Term.pp m pp
          tp)
    | Induct ((id, a, cs), tp) ->
      fprintf fmt "@[Inductive %a %a :=@.%a.@.@.%a@]" Id.pp id pp_pscope a
        pp_constr cs pp tp
    | Import (id, tp) -> fprintf fmt "@[Import %a.@.@.%a@]" Id.pp id pp tp

  and pp_constr fmt cs =
    match cs with
    | [] -> ()
    | (id, a) :: cs ->
      fprintf fmt "@[<v 0>| %a %a@;<1 0>%a@]" Id.pp id pp_pscope a pp_constr cs

  and pp_pscope fmt a =
    match a with
    | PBase a -> pp_tscope fmt a
    | PScope (x, a, b) ->
      if occurs_pscope x b then
        fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" Var.pp x Term.pp
          a pp_pscope b
      else
        fprintf fmt "@[(%a) ->@;<1 2>%a@]" Term.pp a pp_pscope b

  and pp_tscope fmt a =
    match a with
    | TBase a -> Term.pp fmt a
    | TScope (x, a, b) ->
      if occurs_tscope x b then
        fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" Var.pp x Term.pp
          a pp_tscope b
      else
        fprintf fmt "@[(%a) ->@;<1 2>%a@]" Term.pp a pp_tscope b
end
