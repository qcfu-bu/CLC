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

let rec infer ctx t : ty * ctx =
  let pre_t = t in
  let pre_ctx = ctx in
  let ty, ctx =
    match t with
    | Var x ->
      let ty, _, r = find x ctx in
      (ty, add x (ty, One, r) ctx)
    | Ann (t, ty) ->
      let ctx = check ctx t ty in
      (ty, ctx)
    | Type -> (Type, ctx)
    | Linear -> (Type, ctx)
    | TyProd (ty, b) -> (
      let x, b = unbind b in
      let r1, ctx1 = infer_rig ctx ty in
      let r2, ctx2 = infer_rig (add x (ty, Zero, r1) ctx) b in
      let _, r3, _ = find x ctx2 in
      let ctx2 = remove x ctx2 in
      if (r1 = One)
      then
        let () = assert_msg (r3 = Zero) "infer TyProd" in
        (Type, sum ctx1 ctx2)
      else
        (Type, sum ctx1 ctx2))
    | LnProd (ty, b) -> (
      let x, b = unbind b in
      let r1, ctx1 = infer_rig ctx ty in
      let _, ctx2 = infer_rig (add x (ty, Zero, r1) ctx) b in
      let _, r2, _ = find x ctx2 in
      let ctx2 = remove x ctx2 in
      if (r1 = One)
      then
        let () = assert_msg (r2 = Zero) "infer LnProd" in
        (Linear, sum ctx1 ctx2)
      else
        (Linear, sum ctx1 ctx2))
    | Lambda _ -> failwith "infer Lambda"
    | App (t1, t2) -> (
      let t1_ty, ctx1 = infer ctx t1 in
      match whnf t1_ty with
      | TyProd (ty, b) ->
        let r, _ = infer_rig ctx ty in
        let ctx2 = check ctx t2 ty in
        (subst b t2, sum ctx1 (scale r ctx2))
      | LnProd (ty, b) ->
        let r, _ = infer_rig ctx ty in
        let ctx2 = check ctx t2 ty in
        (subst b t2, sum ctx1 (scale r ctx2))
      | _ -> failwith "infer App")
    | Tensor (ty, b) ->
      let x, b = unbind b in
      let r1, ctx1 = infer_rig ctx ty in
      let r2, ctx2 = infer_rig (add x (ty, Zero, r1) ctx) b in
      let _, r3, _ = find x ctx2 in
      let ctx2 = remove x ctx2 in
      if (r1 = One)
      then
        let () = assert_msg (r3 = Zero) "infer Tensor" in
        (type_of_rig (min r1 r2), sum ctx1 ctx2)
      else
        (type_of_rig (min r1 r2), sum ctx1 ctx2)
    | Pair _ -> failwith "infer Pair"
    | LetPair (t, mb) -> (
      let mx, mb = unmbind mb in
      let x1 = mx.(0) in
      let x2 = mx.(1) in
      let t_ty, ctx1 = infer ctx t in
      match whnf t_ty with
      | Tensor (ty, b) ->
        let x, ub = unbind b in
        let r11, _ = infer_rig ctx ty in
        let r12, _ = infer_rig (add x (ty, Zero, r11) ctx) ub in
        let ctx = add x1 (ty, Zero, r11) ctx in
        let ctx = add x2 (subst b (Var x1), Zero, r12) ctx in
        let mb_ty, ctx2 = infer ctx mb in
        let _, r21, _ = find x1 ctx2 in
        let _, r22, _ = find x2 ctx2 in
        let ctx2 = remove x1 ctx2 in
        let ctx2 = remove x2 ctx2 in
        let () = assert_msg (r21 <= r11) "infer LetPair" in
        let () = assert_msg (r22 <= r12) "infer LetPair" in
        let mb_ty = unbox (bind_mvar [| x1; x2 |] (lift mb_ty)) in
        (LetPair (t, mb_ty), sum ctx1 ctx2)
      | _ -> failwith "infer LetPair")
    | LetIn (t, b) ->
      let x, b = unbind b in
      let t_ty, ctx1 = infer ctx t in
      let r1, _ = infer_rig ctx t_ty in
      let b_ty, ctx2 = infer (add x (t_ty, Zero, r1) ctx) b in
      let _, r2, _ = find x ctx2 in
      let ctx2 = remove x ctx2 in
      let () = assert_msg (r2 <= r1) 
        (Format.asprintf "infer LetIn(t := %a; r1 := %a; r2 := %a)"
          Terms.pp t Rig.pp r1 Rig.pp r2)
      in
      (b_ty, sum ctx1 ctx2)
    | Axiom (ty, b) ->
      let x, b = unbind b in
      let ty_ty, _ = infer ctx ty in
      let r1, _ = infer_rig ctx ty in
      let b_ty, ctx = infer (add x (ty, Zero, r1) ctx) b in
      let _, r2, _ = find x ctx in
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

and infer_rig ctx ty : rig * ctx =
  let ty_ty, ctx = infer ctx ty in
  match whnf ty_ty with
  | Type -> (W, ctx)
  | Linear -> (One, ctx)
  | _ -> failwith "infer_rig"

and type_of_rig r = 
  match r with
  | Zero -> failwith "type_of_rig"
  | One -> Linear
  | W -> Type

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
        let ctx = check (add x (ty, Zero, r1) ctx) b1 b2 in
        let _, r2, _ = find x ctx in
        let ctx = remove x ctx in
        let () = assert_msg (r2 <= r1) "check Lambda" in
        let () = print_endline "magic Lambda" in
        let () = iter (fun _ (_, r1, r2) ->
          if r2 = One 
          then assert_msg (r1 = Zero) 
            "affine Lambda cannot use external resource") ctx 
        in
        ctx
      | LnProd (ty, b2) ->
        let x, b1, b2 = unbind2 b1 b2 in
        let r1, _ = infer_rig ctx ty in
        let ctx = check (add x (ty, Zero, r1) ctx) b1 b2 in
        let _, r2, _ = find x ctx in
        let ctx = remove x ctx in
        let () = assert_msg (r2 <= r1) "check Lambda" in
        ctx
      | _ -> failwith "check Lambda")
    | Pair (t1, t2) -> (
      let _ = infer_rig ctx ty in
      match whnf ty with
      | Tensor (ty, b) ->
        let ctx1 = check ctx t1 ty in
        let ctx2 = check ctx t2 (subst b t1) in
        sum ctx1 ctx2
      | _ -> failwith "check Tensor")
    | _ -> 
      let t_ty, ctx = infer ctx t in
      let () = assert_msg (equal t_ty ty) "check" in
      ctx
  in
  let () = debug pre_ctx pre_t ~ty:pre_ty () in
  let () = Format.printf "post_ctx := %a@.\n" pp ctx; in
  ctx