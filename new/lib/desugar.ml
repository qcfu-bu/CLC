open Bindlib
open Util
open Names
open Raw
open Format
module NMap = Map.Make (Name)

type ctx = Terms.t var NMap.t

exception DesugarFind of v

exception DesugarEmpty

let find x ctx =
  try NMap.find x ctx with
  | _ -> raise (DesugarFind x)

let rec desugar (ctx : ctx) t =
  match t with
  | Var x -> Terms._Var (find x ctx)
  | Meta x ->
    let _, xs = Util.unzip (NMap.bindings ctx) in
    let xs = List.map Terms._Var xs in
    Terms._App' (Terms._Meta x) xs
  | Ann (t1, t2) -> Terms._Ann (desugar ctx t1) (desugar ctx t2)
  | U -> Terms._U
  | L -> Terms._L
  | Arrow (v, t1, t2) ->
    let x = Terms.mk (Name.string_of v) in
    let t1 = desugar ctx t1 in
    let ctx = NMap.add v x ctx in
    Terms._Arrow t1 (bind_var x (desugar ctx t2))
  | Lolli (v, t1, t2) ->
    let x = Terms.mk (Name.string_of v) in
    let t1 = desugar ctx t1 in
    let ctx = NMap.add v x ctx in
    Terms._Lolli t1 (bind_var x (desugar ctx t2))
  | Lambda (p, t) -> (
    match p with
    | PVar v ->
      let x = Terms.mk (Name.string_of v) in
      let ctx = NMap.add v x ctx in
      Terms._Lambda (bind_var x (desugar ctx t))
    | _ ->
      let open Terms in
      let x = Terms.mk "x" in
      let p, ctx = desugar_p ctx p in
      let t = desugar ctx t in
      _Lambda (bind_var x (_Match (_Var x) _Mot0 (box_list [ bind_p p t ]))))
  | Fix (v, t) ->
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    Terms._Fix (bind_var x (desugar ctx t))
  | App (t1, t2) -> Terms._App (desugar ctx t1) (desugar ctx t2)
  | LetIn (p, t1, t2) -> (
    match p with
    | PVar v ->
      let x = Terms.mk (Name.string_of v) in
      let t1 = desugar ctx t1 in
      let ctx = NMap.add v x ctx in
      Terms._LetIn t1 (bind_var x (desugar ctx t2))
    | _ ->
      let open Terms in
      let x = mk "x" in
      let t1 = desugar ctx t1 in
      let p, ctx = desugar_p ctx p in
      let t2 = desugar ctx t2 in
      _LetIn t1 (bind_var x (_Match (_Var x) _Mot0 (box_list [ bind_p p t2 ]))))
  | Ind (id, ts) ->
    let ts = List.map (desugar ctx) ts in
    let ts = Terms.box_of_list ts in
    Terms._Ind id ts
  | Constr (id, ts) ->
    let ts = List.map (desugar ctx) ts in
    let ts = Terms.box_of_list ts in
    Terms._Constr id ts
  | Match (t, mot, pb) ->
    let t = desugar ctx t in
    let mot = desugar_mot ctx mot in
    let pb =
      List.map
        (fun (p, b) ->
          let p, ctx = desugar_p ctx p in
          let b = desugar ctx b in
          Terms.bind_p p b)
        pb
    in
    Terms._Match t mot (Terms.box_of_list pb)
  | Axiom (id, t) -> Terms._Axiom id (desugar ctx t)

and desugar_mot ctx mot =
  match mot with
  | Mot0 -> Terms._Mot0
  | Mot1 (p, t) ->
    let p, ctx = desugar_p ctx p in
    Terms._Mot1 (Terms.bind_p p (desugar ctx t))
  | Mot2 (v, p, t) ->
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let p, ctx = desugar_p ctx p in
    Terms._Mot2 (bind_var x (Terms.bind_p p (desugar ctx t)))

and desugar_p ctx p =
  match p with
  | PVar v ->
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    (Terms.PVar x, ctx)
  | PInd (id, ps) ->
    let ps, ctx = desugar_ps ctx ps in
    (Terms.PInd (id, ps), ctx)
  | PConstr (id, ps) ->
    let ps, ctx = desugar_ps ctx ps in
    (Terms.PConstr (id, ps), ctx)

and desugar_ps ctx ps =
  match ps with
  | [] -> ([], ctx)
  | p :: ps ->
    let p, ctx = desugar_p ctx p in
    let ps, ctx = desugar_ps ctx ps in
    (p :: ps, ctx)

let rec desugar_top ctx top =
  match top with
  | Empty -> raise DesugarEmpty
  | Main t -> Terms._Main (desugar ctx t)
  | Define (v, t, top) ->
    let t = desugar ctx t in
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let top = desugar_top ctx top in
    Terms._Define t (bind_var x top)
  | Datype (ind, top) ->
    let tcons = desugar_ind ctx ind in
    let top = desugar_top ctx top in
    Terms._Datype tcons top

and desugar_ind ctx ind =
  let ty = desugar_pscope ctx ind.ty in
  let cs = List.map (desugar_constr ctx) ind.cs in
  Terms._ind ind.id ty (Terms.box_of_list cs)

and desugar_constr ctx constr =
  let ty = desugar_pscope ctx constr.ty in
  Terms._constr constr.id ty

and desugar_pscope ctx pscope =
  match pscope with
  | Pbase tscope ->
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
  | Tbase t ->
    let t = desugar ctx t in
    Terms._TBase t
  | TBind (v, t, tscope) ->
    let t = desugar ctx t in
    let x = Terms.mk (Name.string_of v) in
    let ctx = NMap.add v x ctx in
    let tscope = desugar_tscope ctx tscope in
    Terms._TBind t (bind_var x tscope)

let desugar top = unbox (desugar_top NMap.empty top)

let _ =
  Printexc.register_printer (function
    | DesugarFind v -> Some (asprintf "DesugarFind (%a)" Raw.pp_v v)
    | _ -> None)
