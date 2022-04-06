open Format
open Name

type sort = U | L

type t =
  (* inference *)
  | Ann  of t * t
  | Meta of Meta.t
  (* core *)
  | Knd of sort
  | Var of Var.t
  | Pi  of Var.t * t * t * sort
  | Lam of Var.t * t * sort
  | App of t * t
  | Let of Var.t * t * t
  (* data *)
  | Ind    of Id.t * t list
  | Constr of Id.t * t list
  | Match  of t * m * (p * t) list
  | Fix    of Var.t * t
  (* session *)
  | Main
  | Proto
  | InpEnd
  | OutEnd
  | Inp   of Var.t * t * t
  | Out   of Var.t * t * t
  | Ch    of t
  | Fork  of Var.t * t * t * t
  | Send  of t
  | Recv  of t
  | Close of t
  | Wait  of t
  (* magic *)
  | Axiom of Id.t * t

and p =
  | PInd    of Id.t * Var.t list
  | PConstr of Id.t * Var.t list

and m =
  | Mot0
  | Mot1 of Var.t * t
  | Mot2 of p * t
  | Mot3 of Var.t * p * t

type ind = Id.t * pscope * constr list

and constr = Id.t * pscope

and pscope =
  | PBase  of tscope
  | PScope of Var.t * t * pscope

and tscope =
  | TBase  of t
  | TScope of Var.t * t * tscope

type top =
  | Bottom
  | Define of Var.t * t * top
  | Induct of ind * top

let upren f x =
  Var.case x
    (fun x -> x)
    (fun x -> Var.map ((+) 1) (f x))

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
      | Mot0 ->
        Match (m, Mot0, cls)
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
  | InpEnd -> tm
  | OutEnd -> tm
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
    let m = ren (upren f) m in
    let n = ren f n in
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
  | Wait m ->
    let m = ren f m in
    Wait m
  | Axiom (id, m) ->
    let m = ren f m in
    Axiom (id, m)

let up f x =
  Var.case x
    (fun x -> Var x)
    (fun x -> ren (Var.map @@ (+) 1) (f x))

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
      | Mot0 ->
        Match (m, Mot0, cls)
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
      | Mot3 (x, p, mot) -> (
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
  | InpEnd -> tm
  | OutEnd -> tm
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
    let m = fsubst (up f) m in
    let n = fsubst f n in
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
  | Wait m ->
    let m = fsubst f m in
    Wait m
  | Axiom (id, m) ->
    let m = fsubst f m in
    Axiom (id, m)

let scons m f x =
  Var.case x
    (fun _ -> m)
    (fun x -> f x)

let subst m n = fsubst (scons m (fun x -> Var x)) n

let substn ms n =
  let f =
    List.fold_right
      (fun m acc -> scons m acc) ms (fun x -> Var x)
  in
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
      | Lam (_, bod, _) ->
        whnf (subst n bod)
      | Fix (_, bod) ->
        whnf (App (subst m bod, n))
      | _ -> App (m, n))
  | Let (x, m, n) ->
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
                 match opt, p with
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
  | InpEnd -> tm
  | OutEnd -> tm
  | Inp _ -> tm
  | Out _ -> tm
  | Ch _ -> tm
  | Fork _ -> tm
  | Send _ -> tm
  | Recv _ -> tm
  | Close _ -> tm
  | Wait _ -> tm
  | Axiom _ -> tm

let rec equal t1 t2 =
  if t1 = t2 then
    true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    match t1, t2 with
    | Ann (m1, a1), Ann (m2, a2) ->
      equal m1 m2 && equal a1 a2
    | Meta x1, Meta x2 -> Meta.equal x1 x2
    | Knd s1, Knd s2 -> s1 = s2
    | Var x1, Var x2 -> Var.equal x1 x2
    | Pi (_, a1, b1, s1), Pi (_, a2, b2, s2) ->
      equal a1 a2 && equal b1 b2 && s1 = s2
    | Lam (_, m1, s1), Lam (_, m2, s2) ->
      equal m1 m2 && s1 = s2
    | App (m1, n1), App (m2, n2) ->
      equal m1 m2 && equal n1 n2
    | Let (_, m1, n1), Let (_, m2, n2) ->
      equal m1 m2 && equal n1 n2
    | Ind (id1, ms1), Ind (id2, ms2) ->
      Id.equal id1 id2 && List.equal equal ms1 ms2
    | Constr (id1, ms1), Constr (id2, ms2) ->
      Id.equal id1 id2 && List.equal equal ms1 ms2
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) -> (
        let m = equal m1 m2 in
        let cls =
          List.equal
            (fun (p1, bod1) (p2, bod2) ->
               match p1, p2 with
               | PInd (id1, _), PInd (id2, _) ->
                 Id.equal id1 id2 && equal bod1 bod2
               | PConstr (id1, _), PConstr (id2, _) ->
                 Id.equal id1 id2 && equal bod1 bod2
               | _ -> false)
            cls1 cls2
        in
        m && cls &&
        match mot1, mot2 with
        | Mot0, Mot0 -> true
        | Mot1 (_, mot1), Mot1 (_, mot2) ->
          equal mot1 mot2
        | Mot2 (p1, mot1), Mot2 (p2, mot2) -> (
            match p1, p2 with
            | PInd (id1, _), PInd (id2, _) ->
              Id.equal id1 id2 && equal mot1 mot2
            | PConstr (id1, _), PConstr (id2, _) ->
              Id.equal id1 id2 && equal mot1 mot2
            | _ -> false)
        | Mot3 (_, p1, mot1), Mot3 (_, p2, mot2) -> (
            match p1, p2 with
            | PInd (id1, _), PInd (id2, _) ->
              Id.equal id1 id2 && equal mot1 mot2
            | PConstr (id1, _), PConstr (id2, _) ->
              Id.equal id1 id2 && equal mot1 mot2
            | _ -> false)
        | _ -> false)
    | Fix (_, m1), Fix (_, m2) ->
      equal m1 m2
    | Main, Main -> true
    | Proto, Proto -> true
    | InpEnd, InpEnd -> true
    | OutEnd, OutEnd -> true
    | Inp (_, a1, b1), Inp (_, a2, b2) ->
      equal a1 a2 && equal b1 b2
    | Out (_, a1, b1), Out (_, a2, b2) ->
      equal a1 a2 && equal b1 b2
    | Ch m1, Ch m2 ->
      equal m1 m2
    | Fork (_, a1, m1, n1), Fork (_, a2, m2, n2) ->
      equal a1 a2 && equal m1 m2 && equal n1 n2
    | Send m1, Send m2 ->
      equal m1 m2
    | Recv m1, Recv m2 ->
      equal m1 m2
    | Close m1, Close m2 ->
      equal m1 m2
    | Wait m1, Wait m2 ->
      equal m1 m2
    | Axiom (id1, m1), Axiom (id2, m2) ->
      Id.equal id1 id2 && equal m1 m2
    | _ -> false
