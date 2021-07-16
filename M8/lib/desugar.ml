open Bindlib
open Names
open Raw

module NMap = Map.Make(Name)

type ctx = Terms.t var NMap.t

let find x ctx =
  try NMap.find x ctx
  with _ -> failwith (Format.asprintf "cannot find(%a)" Name.pp x)

let rec desugar (ctx : ctx) t = 
  match t with
  | Var x -> Terms._Var (find x ctx)
  | Ann (t1, t2) -> Terms._Ann (desugar ctx t1) (desugar ctx t2)
  | Type -> Terms._Type
  | Linear -> Terms._Linear
  | TyProd (v, r, t1, t2) -> 
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    Terms._TyProd r (desugar ctx t1) (bind_var x (desugar ctx t2))
  | LnProd (v, r, t1, t2) -> 
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    Terms._LnProd r (desugar ctx t1) (bind_var x (desugar ctx t2))
  | Lambda (p, t) -> (
    match p with
    | PVar v ->
      let x = Terms.mk (Name.string_of v) in
      let ctx = NMap.add v x ctx in
      Terms._Lambda (bind_var x (desugar ctx t))
    | _ ->
      let open Terms in
      let x = mk "x" in
      let p, ctx = desugar_p ctx p in
      let t = desugar ctx t in
      _Lambda (bind_var x 
        (_Match (_Var x) _None 
          (box_list [bind_p p t]))))
  | Fix (v, t) ->
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    Terms._Fix (bind_var x (desugar ctx t))
  | App (t1, t2) ->
    Terms._App (desugar ctx t1) (desugar ctx t2)
  | LetIn (p, r, t1, t2) -> (
    match p with
    | PVar v ->
      let x = Terms.mk (Name.string_of v) in
      let t1 = desugar ctx t1 in
      let ctx = NMap.add v x ctx in
      Terms._LetIn r t1 (bind_var x (desugar ctx t2))
    | _ ->
      let open Terms in
      let x = mk "x" in
      let t1 = desugar ctx t1 in
      let p, ctx = desugar_p ctx p in
      let t2 = desugar ctx t2 in
      _LetIn r t1 (bind_var x 
        (_Match (_Var x) _None 
          (box_list [bind_p p t2]))))
  | TCons (id, ts) ->
    let ts = List.map (desugar ctx) ts in
    let ts = Terms.box_of_list ts in
    Terms._TCons id ts
  | DCons (id, ts) ->
    let ts = List.map (desugar ctx) ts in
    let ts = Terms.box_of_list ts in
    Terms._DCons id ts
  | Match (t, mot, pb) -> (
    let t = desugar ctx t in 
    let mot = desugar_mot ctx mot in
    let pb =
      List.map 
        (fun (p, b) -> 
          let p, ctx = desugar_p ctx p in 
          let b = desugar ctx b in
          Terms.bind_p p b) pb
    in
    Terms._Match t mot (Terms.box_of_list pb))
  | Axiom (id, t) ->
    Terms._Axiom id (desugar ctx t)

and desugar_mot ctx mot =
  match mot with
  | None -> Terms._None
  | Some (v, p, t) ->
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let p, ctx = desugar_p ctx p in
    Terms._Some (bind_var x (Terms.bind_p p (desugar ctx t)))

and desugar_p ctx p =
  match p with
  | PVar v ->
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    (Terms.PVar x, ctx)
  | PTCons (id, ps) ->
    let ps, ctx = desugar_ps ctx ps in
    (Terms.PTCons (id, ps), ctx)
  | PDCons (id, ps) ->
    let ps, ctx = desugar_ps ctx ps in
    (Terms.PDCons (id, ps), ctx)

and desugar_ps ctx ps = 
  match ps with
  | [] -> ([], ctx)
  | p :: ps ->
    let p, ctx = desugar_p ctx p in
    let ps, ctx = desugar_ps ctx ps in
    (p :: ps, ctx)

let rec desugar_top ctx top =
  match top with
  | Empty -> Terms._Empty
  | Define (v, r, t, top) ->
    let t = desugar ctx t in
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let top = desugar_top ctx top in
    Terms._Define r t (bind_var x top)
  | Datype (tcons, top) ->
    let tcons = desugar_tcons ctx tcons in
    let top = desugar_top ctx top in
    Terms._Datype tcons top

and desugar_tcons ctx tcons =
  match tcons with
  | TConstr (id, pscope, dcons) ->
    let pscope = desugar_pscope ctx pscope in
    let dcons = List.map (desugar_dcons ctx) dcons in
    Terms._TConstr id pscope (Terms.box_of_list dcons)

and desugar_dcons ctx dcons =
  match dcons with
  | DConstr (id, pscope) ->
    let pscope = desugar_pscope ctx pscope in
    Terms._DConstr id pscope

and desugar_pscope ctx pscope =
  match pscope with
  | PBase tscope ->
    let tscope = desugar_tscope ctx tscope in
    Terms._PBase tscope
  | PBind (v, t, pscope) ->
    let t = desugar ctx t in
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let pscope = desugar_pscope ctx pscope in
    Terms._PBind t (bind_var x pscope)

and desugar_tscope ctx tscope =
  match tscope with
  | TBase t ->
    let t = desugar ctx t in
    Terms._TBase t
  | TBind (v, r, t, tscope) ->
    let t = desugar ctx t in
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let tscope = desugar_tscope ctx tscope in
    Terms._TBind r t (bind_var x tscope)

let desugar top =
  unbox (desugar_top NMap.empty top)