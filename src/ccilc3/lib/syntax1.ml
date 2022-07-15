open Names

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type 'a abs = Abs of V.t * 'a [@@deriving show { with_path = false }]
and 'a pabs = PAbs of ps * 'a

and tm =
  | Ann of tm * tm
  | Meta of V.t * tms
  | Type of sort
  | Var of V.t
  | Pi of sort * tm * bool * tm abs
  | Fun of tm_opt * cls abs
  | App of tm * tm
  | Let of tm * tm abs
  | Data of D.t * tms
  | Cons of C.t * tms
  | Match of tms * cls
  | If of tm * tm * tm
  | Main
  | Proto
  | End
  | Act of bool * tm * tm abs
  | Ch of bool * tm
  | Fork of tm * tm * tm abs
  | Send of tm
  | Recv of tm
  | Close of tm

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of V.t
  | PCons of C.t * ps
  | PAbsurd

and ps = p list
and cl = Cl of tm_opt pabs
and cls = cl list

type target =
  | TStdin
  | TStdout
  | TStderr
  | TMain
[@@deriving show { with_path = false }]

type decl =
  | DTm of V.t * tm_opt * tm
  | DFun of V.t * tm * cls abs
  | DData of D.t * ptl * dconss
  | DOpen of target * V.t
  | DAxiom of V.t * tm
[@@deriving show { with_path = false }]

and decls = decl list
and dcons = DCons of C.t * ptl
and dconss = dcons list

and ptl =
  | PBase of tl
  | PBind of tm * bool * ptl abs

and tl =
  | TBase of tm
  | TBind of tm * bool * tl abs

let freshen_ps ps =
  let rec aux p =
    match p with
    | PVar x -> PVar (V.freshen x)
    | PCons (c, ps) -> PCons (c, List.map aux ps)
    | PAbsurd -> PAbsurd
  in
  List.map aux ps

let xs_of_ps ps =
  let rec aux p =
    match p with
    | PVar x -> [ x ]
    | PCons (_, ps) -> List.concat_map aux ps
    | PAbsurd -> []
  in
  List.concat_map aux ps

let findi_opt f ls =
  let rec aux k ls =
    match ls with
    | [] -> None
    | h :: t ->
      if f k h then
        Some (k, h)
      else
        aux (k + 1) t
  in
  aux 0 ls

let bindn_tm k xs m =
  let rec aux k m =
    match m with
    | Ann (a, m) ->
      let a = aux k a in
      let m = aux k m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    | Type s -> Type s
    | Var y -> (
      let opt = findi_opt (fun _ x -> V.equal x y) xs in
      match opt with
      | Some (i, _) -> Var (V.bind (i + k))
      | None -> Var y)
    | Pi (s, a, impl, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (s, a, impl, Abs (x, b))
    | Fun (a_opt, Abs (x, cls)) ->
      let a_opt = Option.map (aux k) a_opt in
      let cls =
        List.map
          (fun (Cl (PAbs (ps, m_opt))) ->
            let xs = xs_of_ps ps in
            let k = k + (List.length xs + 1) in
            let m_opt = Option.map (aux k) m_opt in
            Cl (PAbs (ps, m_opt)))
          cls
      in
      Fun (a_opt, Abs (x, cls))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (m, Abs (x, n))
    | Data (d, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Match (ms, cls) ->
      let ms = List.map (aux k) ms in
      let cls =
        List.map
          (fun (Cl (PAbs (ps, m_opt))) ->
            let xs = xs_of_ps ps in
            let k = k + List.length xs in
            let m_opt = Option.map (aux k) m_opt in
            Cl (PAbs (ps, m_opt)))
          cls
      in
      Match (ms, cls)
    | If (m, n1, n2) ->
      let m = aux k m in
      let n1 = aux k n1 in
      let n2 = aux k n2 in
      If (m, n1, n2)
    | Main -> Main
    | Proto -> Proto
    | End -> End
    | Act (r, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (r, a, Abs (x, b))
    | Ch (r, a) -> Ch (r, aux k a)
    | Fork (a, m, Abs (x, n)) ->
      let a = aux k a in
      let m = aux k m in
      let n = aux (k + 1) n in
      Fork (a, m, Abs (x, n))
    | Send m -> Send (aux k m)
    | Recv m -> Recv (aux k m)
    | Close m -> Close (aux k m)
  in
  aux k m

let unbindn_tm k xs m =
  let sz = List.length xs in
  let rec aux k m =
    match m with
    | Ann (a, m) ->
      let a = aux k a in
      let m = aux k m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (aux k) ms in
      Meta (x, ms)
    | Type s -> Type s
    | Var y -> (
      match V.is_bound y sz k with
      | Some i -> Var (List.nth xs (i - k))
      | None -> Var y)
    | Pi (s, a, impl, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (s, a, impl, Abs (x, b))
    | Fun (a_opt, Abs (x, cls)) ->
      let a_opt = Option.map (aux k) a_opt in
      let cls =
        List.map
          (fun (Cl (PAbs (ps, m_opt))) ->
            let xs = xs_of_ps ps in
            let k = k + (List.length xs + 1) in
            let m_opt = Option.map (aux k) m_opt in
            Cl (PAbs (ps, m_opt)))
          cls
      in
      Fun (a_opt, Abs (x, cls))
    | App (m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (m, n)
    | Let (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (m, Abs (x, n))
    | Data (d, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Match (ms, cls) ->
      let ms = List.map (aux k) ms in
      let cls =
        List.map
          (fun (Cl (PAbs (ps, m_opt))) ->
            let xs = xs_of_ps ps in
            let k = k + List.length xs in
            let m_opt = Option.map (aux k) m_opt in
            Cl (PAbs (ps, m_opt)))
          cls
      in
      Match (ms, cls)
    | If (m, n1, n2) ->
      let m = aux k m in
      let n1 = aux k n1 in
      let n2 = aux k n2 in
      If (m, n1, n2)
    | Main -> Main
    | Proto -> Proto
    | End -> End
    | Act (r, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (r, a, Abs (x, b))
    | Ch (r, a) -> Ch (r, aux k a)
    | Fork (a, m, Abs (x, n)) ->
      let a = aux k a in
      let m = aux k m in
      let n = aux (k + 1) n in
      Fork (a, m, Abs (x, n))
    | Send m -> Send (aux k m)
    | Recv m -> Recv (aux k m)
    | Close m -> Close (aux k m)
  in
  aux k m

let bindn_cls k xs cls =
  List.map
    (fun (Cl (PAbs (ps, m_opt))) ->
      let k = k + List.length (xs_of_ps ps) in
      let m_opt = Option.map (bindn_tm k xs) m_opt in
      Cl (PAbs (ps, m_opt)))
    cls

let rec bindn_ptl k xs ptl =
  let rec aux k ptl =
    match ptl with
    | PBase tl -> PBase (bindn_tl k xs tl)
    | PBind (a, impl, Abs (x, ptl)) ->
      let a = bindn_tm k xs a in
      let ptl = aux (k + 1) ptl in
      PBind (a, impl, Abs (x, ptl))
  in
  aux k ptl

and bindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase b -> TBase (bindn_tm k xs b)
    | TBind (a, impl, Abs (x, tl)) ->
      let a = bindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (a, impl, Abs (x, tl))
  in
  aux k tl

let unbindn_cls k xs cls =
  List.map
    (fun (Cl (PAbs (ps, m_opt))) ->
      let k = k + List.length (xs_of_ps ps) in
      let m_opt = Option.map (unbindn_tm k xs) m_opt in
      Cl (PAbs (ps, m_opt)))
    cls

let rec unbindn_ptl k xs ptl =
  let rec aux k ptl =
    match ptl with
    | PBase tl -> PBase (unbindn_tl k xs tl)
    | PBind (a, impl, Abs (x, ptl)) ->
      let a = unbindn_tm k xs a in
      let ptl = aux (k + 1) ptl in
      PBind (a, impl, Abs (x, ptl))
  in
  aux k ptl

and unbindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase a -> TBase (unbindn_tm k xs a)
    | TBind (a, impl, Abs (x, tl)) ->
      let a = unbindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (a, impl, Abs (x, tl))
  in
  aux k tl

let bind_tm x m = Abs (x, bindn_tm 0 [ x ] m)

let bindp_tm_opt p m_opt =
  let xs = xs_of_ps p in
  PAbs (p, Option.map (bindn_tm 0 xs) m_opt)

let bind_cls x cls = Abs (x, bindn_cls 0 [ x ] cls)
let bind_ptl x ptl = Abs (x, bindn_ptl 0 [ x ] ptl)
let bind_tl x tl = Abs (x, bindn_tl 0 [ x ] tl)

let unbind_cls (Abs (x, cls)) =
  let x = V.freshen x in
  (x, unbindn_cls 0 [ x ] cls)

let unbind_tm (Abs (x, m)) =
  let x = V.freshen x in
  (x, unbindn_tm 0 [ x ] m)

let unbindp_tm_opt (PAbs (ps, m_opt)) =
  let ps = freshen_ps ps in
  let xs = xs_of_ps ps in
  (ps, Option.map (unbindn_tm 0 xs) m_opt)

let unbind_ptl (Abs (x, ptl)) =
  let x = V.freshen x in
  (x, unbindn_ptl 0 [ x ] ptl)

let unbind_tl (Abs (x, tl)) =
  let x = V.freshen x in
  (x, unbindn_tl 0 [ x ] tl)

let unbind2_tm (Abs (x, m)) (Abs (_, n)) =
  let x = V.freshen x in
  let m = unbindn_tm 0 [ x ] m in
  let n = unbindn_tm 0 [ x ] n in
  (x, m, n)

let rec equal_p p1 p2 =
  match (p1, p2) with
  | PVar _, PVar _ -> true
  | PCons (c1, ps1), PCons (c2, ps2) ->
    C.equal c1 c2 && List.equal equal_p ps1 ps2
  | PAbsurd, PAbsurd -> true
  | _ -> false

let unbindp2_tm (PAbs (ps1, m)) (PAbs (ps2, n)) =
  if List.equal equal_p ps1 ps2 then
    let ps = freshen_ps ps1 in
    let xs = xs_of_ps ps in
    let m = unbindn_tm 0 xs m in
    let n = unbindn_tm 0 xs n in
    (ps, m, n)
  else
    failwith "unbindp2"

let rec msubst vmap m =
  match m with
  | Ann (a, m) ->
    let a = msubst vmap a in
    let m = msubst vmap m in
    Ann (a, m)
  | Meta (x, ms) ->
    let ms = List.map (msubst vmap) ms in
    Meta (x, ms)
  | Type s -> Type s
  | Var x -> (
    match VMap.find_opt x vmap with
    | Some m -> m
    | None -> Var x)
  | Pi (s, a, impl, abs) ->
    let a = msubst vmap a in
    let x, b = unbind_tm abs in
    let b = msubst vmap b in
    Pi (s, a, impl, bind_tm x b)
  | Fun (a_opt, abs) ->
    let a_opt = Option.map (msubst vmap) a_opt in
    let x, cls = unbind_cls abs in
    let cls =
      List.map
        (fun (Cl pabs) ->
          let p, m_opt = unbindp_tm_opt pabs in
          let m_opt = Option.map (msubst vmap) m_opt in
          Cl (bindp_tm_opt p m_opt))
        cls
    in
    Fun (a_opt, bind_cls x cls)
  | App (m, n) ->
    let m = msubst vmap m in
    let n = msubst vmap n in
    App (m, n)
  | Let (m, abs) ->
    let m = msubst vmap m in
    let x, n = unbind_tm abs in
    let n = msubst vmap n in
    Let (m, bind_tm x n)
  | Data (d, ms) ->
    let ms = List.map (msubst vmap) ms in
    Data (d, ms)
  | Cons (c, ms) ->
    let ms = List.map (msubst vmap) ms in
    Cons (c, ms)
  | Match (ms, cls) ->
    let ms = List.map (msubst vmap) ms in
    let cls =
      List.map
        (fun (Cl pabs) ->
          let p, m_opt = unbindp_tm_opt pabs in
          let m_opt = Option.map (msubst vmap) m_opt in
          Cl (bindp_tm_opt p m_opt))
        cls
    in
    Match (ms, cls)
  | If (m, n1, n2) ->
    let m = msubst vmap m in
    let n1 = msubst vmap n1 in
    let n2 = msubst vmap n2 in
    If (m, n1, n2)
  | Main -> Main
  | Proto -> Proto
  | End -> End
  | Act (r, a, abs) ->
    let a = msubst vmap a in
    let x, b = unbind_tm abs in
    let b = msubst vmap b in
    Act (r, a, bind_tm x b)
  | Ch (r, a) ->
    let a = msubst vmap a in
    Ch (r, a)
  | Fork (a, m, abs) ->
    let a = msubst vmap a in
    let m = msubst vmap m in
    let x, n = unbind_tm abs in
    let n = msubst vmap n in
    Fork (a, m, bind_tm x n)
  | Send m ->
    let m = msubst vmap m in
    Send m
  | Recv m ->
    let m = msubst vmap m in
    Recv m
  | Close m ->
    let m = msubst vmap m in
    Close m

let subst x m n =
  if V.is_blank x then
    m
  else
    msubst (VMap.singleton x n) m

let rec mkApps hd ms =
  match ms with
  | m :: ms -> mkApps (App (hd, m)) ms
  | [] -> hd

let unApps m =
  let rec aux m ns =
    match m with
    | App (m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []
