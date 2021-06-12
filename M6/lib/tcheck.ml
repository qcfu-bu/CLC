open Bindlib
open Terms
open Rig
open Context
open Equality
open Format

let assert_msg cond msg = 
  if cond then ()
  else failwith msg

let is_debug = ref false

let rig_of_sort ty =
  match whnf ty with
  | Type -> W
  | Linear -> One
  | _ -> failwith "Sort Expected"

let sort_of_rig = function
  | W -> Type
  | One -> Linear
  | Zero -> failwith "Non-Zero rig Expected"

let debug pre_ctx t ty post_ctx msg=
  if !is_debug then
  printf "%s\n" msg;
  printf "pre_ctx := %a@." pp pre_ctx;
  printf "@[t  :=@;<1 2>%a@]@." Terms.pp t;
  printf "@[ty :=@;<1 2>%a@]@." Terms.pp ty;
  printf "post_ctx := %a@.@." pp post_ctx

let rec infer_sort ctx ty =
  let ty, ctx = infer (pure ctx) ty in
  match whnf ty with
  | Type -> (W, ctx)
  | Linear -> (One, ctx)
  | _ -> failwith "infer_sort"

and infer ctx t =
  let pre_ctx = ctx in
  let ty, post_ctx =
    match t with
    | Var x ->
      let ty, _, r = find x ctx in
      (ty, add x (ty, One, r) ctx)
    | Ann (t, ty) ->
      let ctx = check ctx t ty in
      (ty, ctx)
    | Type -> (Type, ctx)
    | Linear -> (Linear, ctx)
    | TyProd (ty, b) -> (
      let x, b = unbind b in
      let ty_r, ty_ctx = infer_sort ctx ty in
      let _, b_ctx = infer_sort (add x (ty, Zero, ty_r) ctx) b in
      let x_r = occur x b_ctx in
      let b_ctx = remove x b_ctx in
      if (ty_r = One)
      then
        let () = assert_msg (x_r = Zero) "infer TyProd" in
        (Type, sum ty_ctx b_ctx)
      else
        (Type, sum ty_ctx b_ctx))
    | LnProd (ty, b) -> (
      let x, b = unbind b in
      let ty_r, ty_ctx = infer_sort ctx ty in
      let _, b_ctx = infer_sort (add x (ty, Zero, ty_r) ctx) b in
      let x_r = occur x b_ctx in
      let b_ctx = remove x b_ctx in
      if (ty_r = One)
      then
        let () = assert_msg (x_r = Zero) "infer LnProd" in
        (Linear, sum ty_ctx b_ctx)
      else
        (Linear, sum ty_ctx b_ctx))
    | Lambda _ -> 
      failwith (asprintf "infer Lambda(%a)" Terms.pp t)
    | App (t1, t2) -> (
      let t1_ty, t1_ctx = infer ctx t1 in
      match whnf t1_ty with
      | TyProd (ty, b) -> 
        let ty_r, _ = infer_sort ctx ty in
        let t2_ctx = check ctx t2 ty in
        (subst b t2, sum t1_ctx (scale ty_r t2_ctx))
      | LnProd (ty, b) -> 
        let ty_r, _ = infer_sort ctx ty in
        let t2_ctx = check ctx t2 ty in
        (subst b t2, sum t1_ctx (scale ty_r t2_ctx))
      | _ -> failwith "infer App")
    | LetIn (t, b) ->
      let x, b = unbind b in
      let t_ty, t_ctx = infer ctx t in
      let t_r, _ = infer_sort ctx t_ty in
      let b_ty, b_ctx = infer (add x (t_ty, Zero, t_r) ctx) b in
      let x_r = occur x b_ctx in
      let b_ctx = remove x b_ctx in
      let () = assert_msg (x_r <= t_r)
        (asprintf "infer LetIn(t := %a; t_r := %a; x_r := %a)"
          Terms.pp t Rig.pp t_r Rig.pp x_r)
      in
      (b_ty, sum t_ctx b_ctx)
    | Eq (t1, t2, ty) ->
      let ty_r, ty_ctx = infer_sort ctx ty in
      let () = assert_msg (ty_r = W) "infer Eq" in
      let t1_ctx = check ctx t1 ty in
      let t2_ctx = check ctx t2 ty in
      (Type, sum (sum t1_ctx t2_ctx) ty_ctx)
    | Refl (t, ty) ->
      let ty_r, _ = infer_sort ctx ty in
      let () = assert_msg (ty_r = W) "infer Refl" in
      let t_ctx = check ctx t ty in
      (Eq (t, t, ty), t_ctx)
    | Ind (p, pf, t1, t2, eq, ty) ->
      let ty_r, _ = infer_sort ctx ty in
      let () = assert_msg (ty_r = W) "infer Ind" in
      let x = mk "x" in
      let y = mk "y" in
      let ty = whnf ty in
      let p_ty = unbox
        (_TyProd (lift ty) (bind_var x
          (_TyProd (lift ty) (bind_var y 
            (_Arrow (_Eq (_Var x) (_Var y) (lift ty)) (_Type))))))
      in 
      let _ = check ctx p p_ty in
      let p = Ann (p, p_ty) in
      let pf_ty = unbox
        (_TyProd (lift ty) (bind_var x 
          (_App (_App (_App (lift p) (_Var x)) (_Var x)) 
            (_Refl (_Var x) (lift ty)))))
      in
      let _ = check ctx pf pf_ty in
      let t1_ctx = check ctx t1 ty in
      let t2_ctx = check ctx t2 ty in
      let _ = check ctx eq (Eq (t1, t2, ty)) in
      (whnf (App (App (App (p, t1), t2), eq)), sum t1_ctx t2_ctx)
    | Tensor (ty, b) ->
      let x, b = unbind b in
      let ty_r, ty_ctx = infer_sort ctx ty in
      let b_r, b_ctx = infer_sort (add x (ty, Zero, ty_r) ctx) b in
      let x_r = occur x b_ctx in
      let b_ctx = remove x b_ctx in
      if (ty_r = One)
      then
        let () = assert_msg (x_r = Zero) "infer Tensor" in
        (sort_of_rig (min ty_r b_r), sum ty_ctx b_ctx)
      else
        (sort_of_rig (min ty_r b_r), sum ty_ctx b_ctx)
    | Pair _ -> failwith "infer Pair"
    | LetPair (t, mb) -> (
      let mx, mb = unmbind mb in
      let x1 = mx.(0) in
      let x2 = mx.(1) in
      let t_ty, t_ctx = infer ctx t in
      match whnf t_ty with
      | Tensor (ty, b) ->
        let x, ub = unbind b in
        let ty_r, _ = infer_sort ctx ty in
        let ub_r, _ = infer_sort (add x (ty, Zero, ty_r) ctx) ub in
        let ctx = add x1 (ty, Zero, ty_r) ctx in
        let ctx = add x2 (subst b (Var x1), Zero, ub_r) ctx in
        let mb_ty, mb_ctx = infer ctx mb in
        let x1_r = occur x1 mb_ctx in
        let x2_r = occur x2 mb_ctx in
        let mb_ctx = remove x1 mb_ctx in
        let mb_ctx = remove x2 mb_ctx in
        let () = assert_msg (x1_r <= ty_r) "infer LetPair" in
        let () = assert_msg (x2_r <= ub_r) "infer LetPair" in
        let mb_ty = unbox (bind_mvar [| x1; x2 |] (lift mb_ty)) in
        (LetPair (t, mb_ty), sum t_ctx mb_ctx)
      | _ -> failwith "infer LetPair")
    | CoProd (ty1, ty2) -> (
      let ty1_r, ty1_ctx = infer_sort ctx ty1 in
      let ty2_r, ty2_ctx = infer_sort ctx ty2 in
      (sort_of_rig (min ty1_r ty2_r), sum ty1_ctx ty2_ctx))
    | InjL _ -> failwith "infer InjL"
    | InjR _ -> failwith "infer InjR"
    | Case (t, b1, b2) -> (
      let t_ty, t_ctx = infer ctx t in
      match whnf t_ty with
      | CoProd (ty1, ty2) ->
        let x1, b1 = unbind b1 in
        let x2, b2 = unbind b2 in
        let ty1_r, _ = infer_sort ctx ty1 in
        let ty2_r, _ = infer_sort ctx ty2 in
        let b1_ty, b1_ctx = infer (add x1 (ty1, Zero, ty1_r) ctx) b1 in
        let b2_ty, b2_ctx = infer (add x2 (ty2, Zero, ty2_r) ctx) b2 in
        let x1_r = occur x1 b1_ctx in
        let x2_r = occur x2 b2_ctx in
        let () = assert_msg (x1_r <= ty1_r) "infer Case" in
        let () = assert_msg (x2_r <= ty2_r) "infer Case" in
        let () = assert_msg (equal b1_ty b2_ty) "infer Case" in
        (b1_ty, sum (sum b1_ctx b2_ctx) t_ctx)
      | _ -> failwith "infer Case")
    | Unit -> (Type, ctx)
    | U -> (Unit, ctx)
    | Nat -> (Type, ctx)
    | Zero -> (Nat, ctx)
    | Succ t ->
      let t_ctx = check ctx t Nat in
      (Nat, t_ctx)
    | Iter (p, t1, t2, n) -> (
      let x = mk "x" in
      let p_ty = unbox (_Arrow _Nat (_Type)) in
      let p = Ann (p, p_ty) in
      let t1_ty = App (p, Zero) in
      let t2_ty = unbox
        (_TyProd _Nat (bind_var x
          (_Arrow (_App (lift p) (_Var x))
                  (_App (lift p) (_Succ (_Var x))))))
      in
      let _ = check ctx p p_ty in
      let t1_ctx = check ctx t1 t1_ty in
      let t2_ctx = check ctx t2 t2_ty in
      let n_ctx = check ctx n Nat in
      (whnf (App (p, n)), sum (sum t1_ctx t2_ctx) n_ctx))
    | Channel -> (Linear, ctx)
    | Open -> 
      let ty = _Arrow _Nat _Channel in
      (unbox ty, ctx)
    | Close -> 
      let ty = _Arrow _Channel _Unit in
      (unbox ty, ctx)
    | Read -> 
      let ty = _Arrow _Channel (_Tuple _Nat _Channel) in
      (unbox ty, ctx)
    | Write ->
      let ty = _Arrow (_Tuple _Nat _Channel) _Channel in
      (unbox ty, ctx)
    | PtsTo (t, ty) ->
      let t_ctx = check ctx t Nat in
      let ty_ctx = check ctx ty Type in
      (Linear, sum t_ctx ty_ctx)
    | Ptr ty ->
      let ty_ctx = check ctx ty Type in
      let x = mk "x" in
      let ty = _Tensor _Nat (bind_var x 
        (_PtsTo (_Var x) (lift ty)))
      in
      (unbox ty, ty_ctx)
    | Alloc ->
      let _A = mk "A" in
      let ty = _TyProd _Type (bind_var _A
        (_Arrow (_Var _A) (_Ptr (_Var _A))))
      in
      (unbox ty, ctx)
    | Free ->
      let _A = mk "A" in
      let ty = _TyProd _Type (bind_var _A
        (_Arrow (_Ptr (_Var _A)) _Unit))
      in
      (unbox ty, ctx)
    | Get ->
      let _A = mk "A" in
      let ty = _TyProd _Type (bind_var _A
        (_Arrow (_Ptr (_Var _A)) 
                (_Tuple (_Var _A) (_Ptr (_Var _A)))))
      in
      (unbox ty, ctx)
    | Set ->
      let _A = mk "A" in
      let ty = _TyProd _Type (bind_var _A
        (_Arrow  (_Tuple (_Var _A) (_Ptr (_Var _A)))
                 (_Ptr (_Var _A))))
      in
      (unbox ty, ctx)
  in
  let () = debug pre_ctx t ty post_ctx "infer"  in
  (ty, post_ctx)

and check ctx t ty =
  let pre_ctx = ctx in
  let post_ctx =
    let _ = infer_sort ctx ty in
    match t with
    | Lambda b1 -> (
      match whnf ty with
      | TyProd (ty, b2) as f_ty ->
        let x, b1, b2 = unbind2 b1 b2 in
        let ty_r, _ = infer_sort ctx ty in
        let b1_ctx = check (add x (ty, Zero, ty_r) (pure ctx)) b1 b2 in
        let x_r = occur x b1_ctx in
        let b1_ctx = remove x b1_ctx in
        let () = assert_msg (x_r <= ty_r) 
          (asprintf "check Lambda(x_r := %a, ty_r := %a, f_ty := %a)"
            Rig.pp x_r Rig.pp ty_r Terms.pp f_ty)
        in
        b1_ctx
      | LnProd (ty, b2) as f_ty ->
        let x, b1, b2 = unbind2 b1 b2 in
        let ty_r, _ = infer_sort ctx ty in
        let b1_ctx = check (add x (ty, Zero, ty_r) ctx) b1 b2 in
        let x_r = occur x b1_ctx in
        let b1_ctx = remove x b1_ctx in
        let () = assert_msg (x_r <= ty_r)
          (asprintf "check Lambda(x_r := %a, ty_r := %a, f_ty := %a)"
            Rig.pp x_r Rig.pp ty_r Terms.pp f_ty)
        in
        b1_ctx
      | ty -> failwith 
        (asprintf "check Lambda(ty := %a)" Terms.pp ty))
    | Pair (t1, t2) -> (
      match whnf ty with
      | Tensor (ty, b) ->
        let t1_ctx = check ctx t1 ty in
        let t2_ctx = check ctx t2 (subst b t1) in
        sum t1_ctx t2_ctx
      | _ -> failwith "check Tensor")
    | InjL t -> (
      match whnf ty with
      | CoProd (ty1, _) ->
        check ctx t ty1
      | _ -> failwith "check InjL")
    | InjR t -> (
      match whnf ty with
      | CoProd (_, ty2) ->
        check ctx t ty2
      | _ -> failwith "check InjR")
    | _ ->
      let t_ty, t_ctx = infer ctx t in
      let () = assert_msg (equal t_ty ty) 
        (asprintf "check(t_ty := %a; ty := %a)" 
          Terms.pp t_ty Terms.pp ty)
      in
      t_ctx
  in
  let () = debug pre_ctx t ty post_ctx "check" in
  post_ctx
