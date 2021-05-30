open Bindlib
open Terms
open Context
open Norm
open Equality

let rec check ctx ty q t =
  Format.printf "t := %a\n" pp t;
  Format.printf "q := %d\n" q;
  Format.printf "ty := %a\n\n" pp ty;
  match t with
  | Var x ->
    let ty', q' = find x ctx in
    assert (equal ty ty');
    assert (q' >= q);
    add x ty' (q' - q) ctx
  | Type ->
    assert (equal ty Type);
    ctx
  | Prod (_, t, b) ->
    assert (equal ty Type);
    assert (q = 0);
    assert (is_type ctx t);
    let x, b = unbind b in
    assert (is_type (add x t 0 ctx) b);
    ctx
  | Lambda (q1, t1, b1) -> (
    assert (is_type ctx ty);
    match whnf ty with
    | Prod (q2, t2, b2) ->
      assert (equal t1 t2);
      assert (q1 = q2);
      let x, b1, b2 = unbind2 b1 b2 in
      let ctx = add x t1 (q * q1) ctx in
      let ctx = check ctx b2 q b1 in
      contract x ctx
    | _ -> failwith "CheckLambda")
  | Fix (q', t, b) ->
    assert (is_type ctx ty);
    assert (is_type ctx t);
    let x, b = unbind b in
    let ctx = add x t (q * q') ctx in
    let ctx = check ctx ty q b in
    contract x ctx
  | App (t1, t2) -> (
    let ctx1, ty1 = infer ctx q t1 in
    match whnf ty1 with 
    | Prod (q1, t, b) ->
      let q2 = if q = 0 || q1 = 0 then 0 else 1 in
      let ctx2 = check ctx t q2 t2 in
      let ctx = 
        sub (sum ctx1 (scale q1 ctx2)) (scale q1 ctx) 
      in
      assert (is_positive ctx);
      assert (equal (subst b t2) ty);
      ctx
    | _ -> failwith "Cannot apply non Prod type")
  | Magic -> ctx

and is_type ctx t =
  let ctx = scale 0 ctx in
  let ctx = check ctx Type 0 t in
  is_zero ctx

and infer ctx q t =
  Format.printf "t := %a\n" pp t;
  Format.printf "q := %d\n\n" q;
  match t with
  | Var x ->
    let ty, q' = find x ctx in
    assert (q' >= q);
    (add x ty (q' - q) ctx, ty)
  | Type -> (ctx, Type)
  | Prod _ ->
    let ctx = check ctx Type q t in
    (ctx, Type)
  | Lambda (q', t, b) ->
    assert (is_type ctx t);
    let x, b = unbind b in
    let ctx = add x t (q * q') ctx in
    let ctx, b = infer ctx q b in
    let ctx = contract x ctx in
    let b = unbox (bind_var x (lift b)) in
    (ctx, Prod (q', t, b))
  | Fix (q', t, b) ->
    assert (is_type ctx t);
    let x, b = unbind b in
    let ctx = add x t (q * q') ctx in
    let ctx, ty = infer ctx q b in
    let ctx = contract x ctx in
    (ctx, ty)
  | App (t1, t2) -> (
    let ctx1, ty1 = infer ctx q t1 in
    match whnf ty1 with 
    | Prod (q1, t, b) ->
      let q2 = if q = 0 || q1 = 0 then 0 else 1 in
      let ctx2 = check ctx t q2 t2 in
      let ctx = 
        sub (sum ctx1 (scale q1 ctx2)) (scale q1 ctx) 
      in
      assert (is_positive ctx);
      (ctx, (subst b t2))
    | _ -> failwith "Cannot apply non Prod type")
  | Magic -> (ctx, Magic)