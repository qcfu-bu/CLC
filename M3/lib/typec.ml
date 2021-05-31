open Bindlib
open Rig
open Terms
open Norms
open Context
open Equality

let rec check ctx t p ty =
  Format.printf "check\n";
  Format.printf "ctx := %a\n" Context.pp ctx;
  Format.printf "t   := %a\n" Terms.pp t;
  Format.printf "q   := %a\n" Rig.pp p;
  Format.printf "ty  := %a\n" Terms.pp ty;
  Format.printf "\n";
  match t with
  | Lambda b -> (
    let ctx = check ctx ty _Zero Type in
    match whnf ty with
    | Prod (q, t', b') -> 
      let x, b, b' = unbind2 b b' in
      let ctx = add x (t', _Zero) ctx in
      let ctx = check ctx b _One b' in
      let _, q' = find x ctx in
      assert (q' <= q);
      scale p (remove x ctx)
    | _ -> failwith "Lambda")
  | Fix b -> (
    let x, b = unbind b in
    let ctx = check ctx ty _Zero Type in
    let ctx = add x (ty, _Zero) ctx in
    let ctx = check ctx b _One ty in
    let _, q = find x ctx in
    assert (p = q);
    scale p (remove x ctx))
  | _ ->  
    let ctx, ty' = infer ctx p t in
    assert (equal ty ty');
    ctx

and infer ctx p t = 
  Format.printf "infer\n";
  Format.printf "ctx := %a\n" Context.pp ctx;
  Format.printf "t   := %a\n" Terms.pp t;
  Format.printf "q   := %a\n" Rig.pp p;
  Format.printf "\n";
  match t with
  | Var x ->
    let ty, q = find x ctx in
    assert (q = _Zero);
    (add x (ty, p) ctx, ty)
  | Ann (t, ty) ->
    (check ctx t p ty, ty)
  | Type -> ctx, Type
  | Prod (_, t, b) ->
    let x, b = unbind b in
    let ctx = check ctx t _Zero Type in
    let ctx = add x (t, _Zero) ctx in
    let ctx = check ctx b _Zero Type in
    let _, q = find x ctx in
    assert (q = _Zero);
    (remove x ctx, Type)
  | App (s, t) -> (
    let ctx1, ty = infer ctx p s in
    match whnf ty with
    | Prod (q, t', b') ->
      let ctx2 = check ctx t (p * q)  t' in
      assert (same ctx1 ctx2);
      (sum ctx1 ctx2, subst b' t)
    | _ -> failwith "App")
  | _ -> failwith "Infer"