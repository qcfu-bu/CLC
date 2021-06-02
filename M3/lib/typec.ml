open Bindlib
open Rig
open Terms
open Norms
open Context
open Equality

let assert_check cond msg ctx t p ty =
  try assert cond
  with _ ->
    Format.printf "check error\n";
    Format.printf "msg := %s\n" msg;
    Format.printf "ctx := %a@." Context.pp ctx;
    Format.printf "@[t   :=@;<1 2> %a@]@." Terms.pp t;
    Format.printf "@[q   :=@;<1 2> %a@]@." Rig.pp p;
    Format.printf "@[ty  :=@;<1 2> %a@]@." Terms.pp ty;
    Format.printf "\n";
    assert false

let assert_infer cond msg ctx p t =
  try assert cond
  with _ ->
    Format.printf "infer error\n";
    Format.printf "ctx := %a@." Context.pp ctx;
    Format.printf "@[t   :=@;<1 2> %a@]@." Terms.pp t;
    Format.printf "@[q   :=@;<1 2> %a@]@." Rig.pp p;
    Format.printf "\n";
    assert false

let rec check ctx t p ty =
  let pre_ctx = ctx in
  let pre_t = t in
  let pre_p = p in
  let pre_ty = ty in
  let ctx = 
    match t with
    | Lambda b -> (
      match whnf ty with
      | Prod (q, t', b') -> 
        let x, b, b' = unbind2 b b' in
        let ctx = add x (t', _Zero) ctx in
        let ctx = check ctx b _One b' in
        let _, q' = find x ctx in
        assert_check (q' <= q)
          (Format.asprintf "Lambda %a <= %a" Rig.pp q' Rig.pp q)
          pre_ctx pre_t pre_p pre_ty;
        scale p (remove x ctx)
      | _ -> failwith "Lambda")
    | Fix b -> (
      let x, b = unbind b in
      let ctx = check ctx ty _Zero Type in
      let ctx = add x (ty, _Zero) ctx in
      let ctx = check ctx b _One ty in
      let _, q = find x ctx in
      assert_check (q <= p) "Fix"  
        pre_ctx pre_t pre_p pre_ty;
      scale p (remove x ctx))
    | _ ->  
      let ctx, ty' = infer ctx p t in
      assert_check (equal ty ty') "Infer" 
        pre_ctx pre_t pre_p pre_ty;
      ctx
  in
  Format.printf "check\n";
  Format.printf "ctx := %a@." Context.pp pre_ctx;
  Format.printf "@[t   :=@;<1 2> %a@]@." Terms.pp pre_t;
  Format.printf "@[q   :=@;<1 2> %a@]@." Rig.pp pre_p;
  Format.printf "@[ty  :=@;<1 2> %a@]@." Terms.pp pre_ty;
  Format.printf "\n";
  ctx

and infer ctx p t = 
  let pre_ctx = ctx in
  let pre_p = p in
  let pre_t = t in
  let ctx, ty =
    match t with
    | Var x ->
      let ty, q = find x ctx in
      assert_infer (q = _Zero) "Var" 
        pre_ctx pre_p pre_t;
      (add x (ty, p) ctx, ty)
    | AnnTy (t, ty) ->
      (check ctx t p ty, ty)
    | AnnVr (_, x) ->
      let ty, q = find x ctx in
      assert_infer (q = _Zero) "AnnVr"
        pre_ctx pre_p pre_t;
      (add x (ty, p) ctx, ty)
    | Type -> ctx, Type
    | Prod (_, t, b) ->
      let x, b = unbind b in
      let ctx = check ctx t _Zero Type in
      let ctx = add x (t, _Zero) ctx in
      let ctx = check ctx b _Zero Type in
      let _, q = find x ctx in
      assert_infer (p = _Zero) "Prod"
        pre_ctx pre_p pre_t;
      assert_infer (q = _Zero) "Prod"
        pre_ctx pre_p pre_t;
      (remove x ctx, Type)
    | App (s, t) -> (
      let ctx1, ty = infer ctx p s in
      match whnf ty with
      | Prod (q, t', b') ->
        let ctx2 = check ctx t (p * q)  t' in
        assert_infer (same ctx1 ctx2) "App"
          pre_ctx pre_p pre_t;
        (sum ctx1 ctx2, subst b' t)
      | _ -> failwith "App")
    | LetIn (q, t, b) ->
      let x, _ = unbind b in
      let ctx1, ty1 = infer ctx (p * q) t in
      let ctx = add x (ty1, _Zero) ctx in
      let t = AnnVr (t, x) in
      let ctx2, ty2 = infer ctx _One (subst b t) in
      let _, q' = find x ctx2 in
      let ctx2 = remove x ctx2 in
      assert_infer (q' <= q) 
        (Format.asprintf "LetIn %a <= %a" Rig.pp q' Rig.pp q)
        pre_ctx pre_p pre_t;
      assert_infer (same ctx1 ctx2) 
        (Format.asprintf "LetIn\nctx1 := %a\nctx2 := %a\n" 
          Context.pp ctx1 Context.pp ctx2)
        pre_ctx pre_p pre_t;
      (sum ctx1 (scale p ctx2), ty2)
    | Axiom (q, t, b) ->
      let x, b = unbind b in
      let ctx = check ctx t _Zero Type in
      let ctx = add x (t, _Zero) ctx in
      let ctx, ty = infer ctx _One b in
      let _, q' = find x ctx in
      let ctx = remove x ctx in
      assert_infer (q' <= q) 
        (Format.asprintf "Axiom %a <= %a" Rig.pp q' Rig.pp q)
        pre_ctx pre_p pre_t;
      (ctx, ty)
    | _ -> 
      assert_infer false "Infer" pre_ctx pre_p pre_t;
      failwith ""
  in
  Format.printf "infer\n";
  Format.printf "ctx := %a@." Context.pp pre_ctx;
  Format.printf "@[t   :=@;<1 2> %a@]@." Terms.pp pre_t;
  Format.printf "@[q   :=@;<1 2> %a@]@." Rig.pp pre_p;
  Format.printf "@[ty  :=@;<1 2> %a@]@." Terms.pp ty;
  Format.printf "\n";
  (ctx, ty)
  