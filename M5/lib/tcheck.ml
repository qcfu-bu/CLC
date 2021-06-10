open Bindlib
open Rig
open Terms
open Context
open Equality

let assert_msg cond msg = 
  if cond then ()
  else failwith msg

let is_debug = ref false

let debug ctx t ?ty:ty () =
  if !is_debug then
  match ty with
  | Some ty ->
    Format.printf "check\n";
    Format.printf "pre_ctx := %a@." pp ctx;
    Format.printf "@[t  :=@;<1 2>%a@]@." Terms.pp t;
    Format.printf "@[ty :=@;<1 2>%a@]@." Terms.pp ty;
  | None ->
    Format.printf "infer\n";
    Format.printf "pre_ctx := %a@." pp ctx;
    Format.printf "@[t  :=@;<1 2>%a@]@." Terms.pp t

let rec infer ctx t =
  let pre_t = t in
  let pre_ctx = ctx in
  let ty, ctx =
    match t with
    | Var x ->
      let ty, _ = find x ctx in
      (ty, add x (ty, One) ctx)
    | Ann (t, ty) ->
      let ctx = check ctx t ty in
      (ty, ctx)
    | Type -> (Type, ctx)
    | Linear -> (Type, ctx)
    | TyProd (ty, b) -> (
      let x, b = unbind b in
      let r1, ctx1 = infer_rig ctx ty in
      let r2, ctx2 = infer_rig (add x (ty, Zero) ctx) b in
      let _, r3 = find x ctx2 in
      if (r1 = One)
      then
        let () = assert_msg (r2 = One) "infer TyProd" in
        let () = assert_msg (r3 = Zero) "infer TyProd" in
        (Type, sum ctx1 ctx2)
      else
        (Type, sum ctx1 ctx2))
    | LnProd (ty, b) -> (
      let x, b = unbind b in
      let r1, ctx1 = infer_rig ctx ty in
      let r2, ctx2 = infer_rig (add x (ty, Zero) ctx) b in
      let _, r3 = find x ctx2 in
      if (r1 = One)
      then
        let () = assert_msg (r2 = One) "infer LnProd" in
        let () = assert_msg (r3 = Zero) "infer LnProd" in
        (Linear, sum ctx1 ctx2)
      else
        (Linear, sum ctx1 ctx2))
    | Lambda _ -> failwith "infer Lambda"
    | App (t1, t2) -> (
      let t1_ty, ctx1 = infer ctx t1 in
      match whnf t1_ty with
      | TyProd (ty, b) ->
        let _ = infer_rig ctx ty in
        let ctx2 = check ctx t2 ty in
        (subst b t2, sum ctx1 ctx2)
      | LnProd (ty, b) ->
        let _ = infer_rig ctx ty in
        let ctx2 = check ctx t2 ty in
        (subst b t2, sum ctx1 ctx2)
      | _ -> failwith "infer App")
    | LetIn (t, b) ->
      let x, b = unbind b in
      let t_ty, ctx1 = infer ctx t in
      let r1, _ = infer_rig ctx t_ty in
      let b_ty, ctx2 = infer (add x (t_ty, Zero) ctx) b in
      let _, r2 = find x ctx2 in
      let ctx2 = remove x ctx2 in
      let () = assert_msg (r2 <= r1) "LetIn" in
      (b_ty, sum ctx1 ctx2)
    | Axiom (ty, b) ->
      let x, b = unbind b in
      let ty_ty, _ = infer ctx ty in
      let r1, _ = infer_rig ctx ty in
      let b_ty, ctx = infer (add x (ty, Zero) ctx) b in
      let _, r2 = find x ctx in
      let ctx = remove x ctx in
      let () = assert_msg (r2 <= r1) 
        (Format.asprintf "Axiom(x := %s; ty := %a; ty_ty := %a; r1 := %a; r2 := %a)" 
          (name_of x) Terms.pp ty Terms.pp ty_ty Rig.pp r1 Rig.pp r2)
      in
      (b_ty, ctx)
  in
  let () = debug pre_ctx pre_t () in
  let () = Format.printf "post_ctx := %a@.\n" pp ctx; in
  (ty, ctx)


and infer_rig ctx ty =
  let ty_ty, ctx = infer ctx ty in
  match whnf ty_ty with
  | Type -> (W, ctx)
  | Linear -> (One, ctx)
  | _ -> failwith "infer_rig"

and check ctx t ty = 
  let pre_ctx = ctx in
  let pre_t = t in
  let pre_ty = ty in
  let ctx =
    match t with
    | Lambda b1 -> (
      let _ = infer_rig ctx ty in
      match whnf ty with
      | TyProd (ty, b2) ->
        let x, b1, b2 = unbind2 b1 b2 in
        let r1, _ = infer_rig ctx ty in
        let ctx = check (add x (ty, Zero) ctx) b1 b2 in
        let _, r2 = find x ctx in
        let ctx = remove x ctx in
        let () = assert_msg (r2 <= r1) "check Lambda" in
        ctx
      | LnProd (ty, b2) ->
        let x, b1, b2 = unbind2 b1 b2 in
        let r1, _ = infer_rig ctx ty in
        let ctx = check (add x (ty, Zero) ctx) b1 b2 in
        let _, r2 = find x ctx in
        let ctx = remove x ctx in
        let () = assert_msg (r2 <= r1) "check Lambda" in
        ctx
      | _ -> failwith "check Lambda")
    | _ -> 
      let t_ty, ctx = infer ctx t in
      let () = assert_msg (equal t_ty ty) "check" in
      ctx
  in
  let () = debug pre_ctx pre_t ~ty:pre_ty () in
  let () = Format.printf "post_ctx := %a@.\n" pp ctx; in
  ctx