open Bindlib
open Ring
open Terms
open Context
open Norm
open Equality

let d = ref false

let rec check ctx ty q t =
  if !d then begin
    Format.printf "check\n";
    Format.printf "ctx := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx;
    Format.printf "\n";
    Format.printf "t   := %a\n" pp t;
    Format.printf "q   := %a\n" Ring.pp q;
    Format.printf "ty  := %a\n\n" pp ty;
  end;
  assert (q = z || q = o);
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
    assert (q = z);
    assert (is_type ctx t);
    let x, b = unbind b in
    assert (is_type (add x t z ctx) b);
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
  | LetIn (q1, t1, t2, b) ->
    assert (is_type ctx t1);
    let q2 = if q = z || q1 = z then z else o in
    let ctx2 = check ctx t1 q2 t2 in
    let x, b = unbind b in
    let ctx1, b = infer (add x t1 (q * q1) ctx) q b in
    let ctx1 = contract x ctx1 in
    Format.printf "ctx1 := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx1;
    Format.printf "\n";
    Format.printf "ctx2 := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx2;
    Format.printf "\n";
    let b = unbox (bind_var x (lift b)) in
    assert (equal (subst b t2) ty);
    assert (Context.equal ctx1 ctx2);
    Format.printf "ctx  := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx;
    Format.printf "\n";
    let ctx = sum ctx1 (scale q1 (sub ctx2 ctx)) in
    Format.printf "ctx' := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx;
    Format.printf "\n";
    Format.printf "q1   := %a\n" Ring.pp q1;
    Format.printf "CheckContract(%s)\n\n" (name_of x);
    assert (is_positive ctx);
    ctx
  | App (t1, t2) -> (
    let ctx1, ty1 = infer ctx q t1 in
    match whnf ty1 with 
    | Prod (q1, t, b) ->
      let q2 = if q = z || q1 = z then z else o in
      let ctx2 = check ctx t q2 t2 in
      assert (Context.equal ctx1 ctx2);
      let ctx = sum ctx1 (scale q1 (sub ctx2 ctx)) in
      assert (is_positive ctx);
      assert (equal (subst b t2) ty);
      ctx
    | _ -> failwith "Cannot apply non Prod type")
  | Magic -> ctx

and is_type ctx t =
  let ctx = scale z ctx in
  let ctx = check ctx Type z t in
  is_zero ctx

and infer ctx q t =
  if !d then begin
    Format.printf "infer\n";
    Format.printf "ctx := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx;
    Format.printf "\n";
    Format.printf "t   := %a\n" pp t;
    Format.printf "q   := %a\n\n" Ring.pp q;
  end;
  assert (q = z || q = o);
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
  | LetIn (q1, t1, t2, b) ->
    assert (is_type ctx t1);
    let q2 = if q = z || q1 = z then z else o in
    let ctx2 = check ctx t1 q2 t2 in
    let x, b = unbind b in
    let ctx1, b = infer (add x t1 (q * q1) ctx) q b in
    let ctx1 = contract x ctx1 in
    Format.printf "ctx1 := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx1;
    Format.printf "\n";
    Format.printf "ctx2 := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx2;
    Format.printf "\n";
    let b = unbox (bind_var x (lift b)) in
    let ty = subst b t2 in
    assert (Context.equal ctx1 ctx2);
    Format.printf "ctx  := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx;
    Format.printf "\n";
    let ctx = sum ctx1 (scale q1 (sub ctx2 ctx)) in
    Format.printf "ctx' := ";
    iter (fun x (t, q) -> 
      Format.printf "[%s :%a %a] " (name_of x) Ring.pp q pp t) ctx;
    Format.printf "\n";
    Format.printf "q1   := %a\n" Ring.pp q1;
    Format.printf "InferContract(%s)\n\n" (name_of x);
    assert (is_positive ctx);
    (ctx, ty)
  | App (t1, t2) -> (
    let ctx1, ty1 = infer ctx q t1 in
    match whnf ty1 with 
    | Prod (q1, t, b) ->
      let q2 = if q = z || q1 = z then z else o in
      let ctx2 = check ctx t q2 t2 in
      assert (Context.equal ctx1 ctx2);
      let ctx = sum ctx1 (scale q1 (sub ctx2 ctx)) in
      assert (is_positive ctx);
      (ctx, (subst b t2))
    | _ -> failwith "Cannot apply non Prod type")
  | Magic -> (ctx, Magic)