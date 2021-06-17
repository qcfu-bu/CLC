open Bindlib
open Format
open Rig
open Terms
open Context
open Equality

let assert_msg cond msg = 
  if cond then ()
  else failwith msg

let rig_of_sort ty =
  match whnf ty with
  | Type -> W
  | Linear -> One
  | _ -> failwith "sort expected"

let sort_of_rig = function
  | W -> Type
  | One -> Linear
  | Zero -> failwith "non-Zero rig expected"

let rec infer_sort v_ctx id_ctx ty =
  let sort, v_ctx = infer (pure v_ctx) id_ctx ty in
  match whnf sort with
  | Type   -> (W, v_ctx)
  | Linear -> (One, v_ctx)
  | sort   -> 
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp sort)

and infer v_ctx id_ctx t =
  match t with
  | Var x ->
    let ty, _, m = find x v_ctx in
    (ty, VarMap.add x (ty, One, m) v_ctx)
  | Ann (t, ty) -> (
    match t with
    | LetIn (t, pb) ->
      let p, b = unbind_p pb in
      let pb = unbox (bind_p p (lift (Ann (b, ty)))) in
      let v_ctx = check v_ctx id_ctx (LetIn (t, pb)) ty in
      (ty, v_ctx)
    | _ ->
      let v_ctx = check v_ctx id_ctx t ty in
      (ty, v_ctx))
  | Type -> (Type, v_ctx)
  | Linear -> (Type, v_ctx)
  | TyProd (ty, b) ->
    let x, b = unbind b in
    let sort, v_ctx1 = infer_sort v_ctx id_ctx ty in
    let _, v_ctx2 = 
      infer_sort (VarMap.add x (ty, Zero, sort) v_ctx) id_ctx b 
    in
    let v_ctx2 = VarMap.remove x v_ctx2 in
    (Type, merge v_ctx1 v_ctx2)
  | LnProd (ty, b) ->
    let x, b = unbind b in
    let sort, v_ctx1 = infer_sort v_ctx id_ctx ty in
    let _, v_ctx2 = 
      infer_sort (VarMap.add x (ty, Zero, sort) v_ctx) id_ctx b 
    in
    let v_ctx2 = VarMap.remove x v_ctx2 in
    (Linear, merge v_ctx1 v_ctx2)
  | Lambda _ -> failwith (asprintf "infer Lambda(%a)" Terms.pp t)
  | Fix _ -> failwith (asprintf "infer Fix(%a)" Terms.pp t)
  | App (t1, t2) -> (
    let ty1, v_ctx1 = infer v_ctx id_ctx t1 in
    match whnf ty1 with
    | TyProd (ty, b) ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx2 = check v_ctx id_ctx t2 ty in
      (subst b t2, merge v_ctx1 (scale m v_ctx2))
    | LnProd (ty, b) ->
      let m, _ = infer_sort v_ctx id_ctx ty in
      let v_ctx2 = check v_ctx id_ctx t2 ty in
      (subst b t2, merge v_ctx1 (scale m v_ctx2))
    | _ -> failwith (asprintf "infer App(t := %a)" Terms.pp t))
  | LetIn (t, pb) -> (
    let p, b = unbind_p pb in
    match p with
    | PVar x ->
      let ty1, v_ctx1 = infer v_ctx id_ctx t in 
      let m, _ = infer_sort v_ctx id_ctx ty1 in
      let ty2, v_ctx2 = 
        if m = W && is_pure v_ctx1 then
          infer v_ctx id_ctx (subst_p pb t)
        else 
          let ty2, v_ctx2 = 
            infer (VarMap.add x (ty1, Zero, m) v_ctx) id_ctx b
          in
          let r = occur x v_ctx2 in
          let v_ctx2 = VarMap.remove x v_ctx2 in
          assert_msg (r <= m)
            (asprintf "infer LetIn(t := %a; m := %a; r := %a)"
              Terms.pp t Rig.pp m Rig.pp r);
          (ty2, v_ctx2)
      in
      (ty2, merge v_ctx1 v_ctx2)
    | _ -> infer v_ctx id_ctx (Match (t, None, [pb])))
  | TCons (id, ts) ->
    let TConstr (_, tscope, _) = IdMap.find id id_ctx in
    check_scope v_ctx id_ctx ts tscope
  | DCons (id, ts) ->
    let DConstr (_, tscope) = find_dcons id id_ctx in
    check_scope v_ctx id_ctx ts tscope
  | Match _ -> ??
  | Axiom (_, ty) ->
    let _ = infer_sort v_ctx id_ctx ty in
    (ty, v_ctx)

and check v_ctx id_ctx t = ??

and infer_pbinder v_ctx id_ctx = ??

and check_scope v_ctx id_ctx ts tscope =
  match ts, tscope with
  | t :: ts, Bind (ty, tscope) ->
    let v_ctx1 = check v_ctx id_ctx t ty in
    let ty, v_ctx2 = check_scope v_ctx id_ctx ts (subst tscope t) in
    (ty, merge v_ctx1 v_ctx2)
  | [], Base ty -> (ty, v_ctx)
  | _ -> failwith "check_scope"