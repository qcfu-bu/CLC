open Bindlib
open Terms
open Norms
open Context
open Equality

let assert_msg cond msg = 
  if cond then ()
  else failwith msg

let debug ictx ?lctx:lctx t ?ty:ty () =
  match lctx, ty with
  | Some lctx, Some ty ->
    Format.printf "check_l\n";
    Format.printf "ictx := %a@." pp_ctx ictx;
    Format.printf "lctx := %a@." pp_ctx lctx;
    Format.printf "@[t  :=@;<1 2>%a@]@." pp t;
    Format.printf "@[ty :=@;<1 2>%a@]@." pp ty;
    Format.printf "\n"
  | Some lctx, None ->
    Format.printf "infer_l\n";
    Format.printf "ictx := %a@." pp_ctx ictx;
    Format.printf "lctx := %a@." pp_ctx lctx;
    Format.printf "@[t  :=@;<1 2>%a@]@." pp t;
    Format.printf "\n"
  | None, Some ty ->
    Format.printf "check_i\n";
    Format.printf "ictx := %a@." pp_ctx ictx;
    Format.printf "@[t  :=@;<1 2>%a@]@." pp t;
    Format.printf "@[ty :=@;<1 2>%a@]@." pp ty;
    Format.printf "\n"
  | None, None ->
    Format.printf "infer_i\n";
    Format.printf "ictx := %a@." pp_ctx ictx;
    Format.printf "@[t  :=@;<1 2>%a@]@." pp t;
    Format.printf "\n"

let rec infer_i ictx t = 
  let () = debug ictx t () in
  match t with
  | Var x -> find x ictx
  | Ann (t, ty) -> 
    let () = check_i ictx t ty in
    ty
  | Type _ -> Type I
  | Prod (ty, b) -> (
    let x, b = unbind b in
    let () = check_i ictx ty (Type I) in
    let ictx = add x ty ictx in
    let b = infer_i ictx b in
    match whnf b with
    | Type m -> Type m
    | _ -> failwith "infer_i Prod")
  | Lolli (ty1, ty2) ->
    let () = check_i ictx ty1 (Type L) in
    let () = check_i ictx ty2 (Type L) in
    Type L
  | Lambda _ -> failwith "infer_i Lambda"
  | App (t1, t2) -> (
    let ty = infer_i ictx t1 in
    match whnf ty with
    | Prod (ty, b) ->
      let () = check_i ictx t2 ty in
      subst b t2
    | _ -> failwith "infer_i Prod")
  | LetIn (t, b) -> (
    let ty = infer_i ictx t in
    let () = check_i ictx ty (Type I) in
    infer_i ictx (subst b t))
  | Eq (t1, t2, ty) ->
    let () = check_i ictx ty (Type I) in
    let () = check_i ictx t1 ty in
    let () = check_i ictx t2 ty in
    Type I
  | Refl t ->
    let ty = infer_i ictx t in
    Eq (t, t, ty)
  | Ind (p, pf, t1, t2, eq) -> (
    let p_ty = infer_i ictx p in
    match p_ty with
    | Prod (ty, _) ->
      let x = mk "x" in
      let y = mk "y" in
      let ty = whnf ty in
      let p_ty' = unbox
        (_Prod (lift ty) (bind_var x
          (_Prod (lift ty) (bind_var y 
            (_Arrow (_Eq (_Var x) (_Var y) (lift ty)) (_Type I))))))
      in
      let () = assert_msg (equal p_ty p_ty') "infer_i Ind" in
      let pf_ty = unbox
        (_Prod (lift ty) (bind_var x 
          (_App (_App (_App (lift p) (_Var x)) (_Var x)) 
            (_Refl (_Var x)))))
      in
      let () = check_i ictx pf pf_ty in
      let () = check_i ictx t1 ty in
      let () = check_i ictx t2 ty in
      let () = check_i ictx eq (Eq (t1, t2, ty)) in
      whnf (App (App (App (p, t1), t2), eq))
    | _ -> failwith "infer_i Ind")
  | G ty ->
    let () = check_i ictx ty (Type L) in
    Type I
  | G_intro t ->
    let ty, lctx, slack = infer_l ictx empty t in
    let () = assert_msg (is_empty lctx || slack) "infer_i G_intro" in
    G ty
  | G_elim _ -> failwith "infer_i G_elim"
  | F (ty, b) ->
    let x, b = unbind b in
    let () = check_i ictx ty (Type I) in
    let ictx = add x ty ictx in
    let () = check_i ictx b (Type L) in
    Type L
  | F_intro _ -> failwith "infer_i F_intro"
  | F_elim _ -> failwith "infer_i F_elim"
  | Sum (ty, b) ->
    let x, b = unbind b in
    let () = check_i ictx ty (Type I) in
    let ictx = add x ty ictx in
    let () = check_i ictx b (Type I) in
    Type I
  | Tensor (ty1, ty2) ->
    let () = check_i ictx ty1 (Type L) in
    let () = check_i ictx ty2 (Type L) in
    Type L
  | And (ty1, ty2) ->
    let () = check_i ictx ty1 (Type L) in
    let () = check_i ictx ty2 (Type L) in
    Type L
  | Pair _ -> failwith "infer_i Pair"
  | Proj1 t -> (
    let ty = infer_i ictx t in
    match whnf ty with
    | Sum (ty, _) -> ty
    | _ -> failwith "infer_i Proj1")
  | Proj2 t -> (
    let ty = infer_i ictx t in
    match whnf ty with
    | Sum (_, b) -> subst b (Proj2 t)
    | _ -> failwith "infer_i Proj2")
  | Tensor_elim _ -> failwith "infer_i Tensor_elim"
  | Unit m -> Type m
  | True -> Type L
  | U -> Unit I
  | Unit_elim _ -> failwith "infer_i Unit_elim"
  | Axiom (ty, b) -> 
    let x, b = unbind b in
    let () = check_i ictx ty (Type I) in
    let ictx = add x ty ictx in
    infer_i ictx b

and check_i ictx t ty =
  let () = debug ictx t ~ty:ty () in
  match t with
  | Lambda t -> (
    let () = check_i ictx ty (Type I) in
    match whnf ty with
    | Prod (ty, b) ->
      let x, t, b = unbind2 t b in
      let ictx = add x ty ictx in
      check_i ictx t b
    | _ -> failwith "check_i Lambda")
  | Pair (t1, t2) -> (
    let () = check_i ictx ty (Type I) in
    match whnf ty with
    | Sum (ty1, b) ->
      let () = check_i ictx t1 ty1 in
      check_i ictx t2 (subst b t1)
    | _ -> failwith "check_i Pair")
  | _ -> 
    let t = infer_i ictx t in
    assert_msg (equal t ty) 
    (Format.asprintf "\ncheck_i\n t  := %a\n ty := %a" pp t pp ty)

and infer_l ictx lctx t = 
  let () = debug ictx ~lctx:lctx t () in
  match t with
  | Var x ->
    let ty = find x lctx in
    let lctx = remove x lctx in
    (ty, lctx, false)
  | Ann (t, ty) ->
    let lctx, slack = check_l ictx lctx t ty in
    (ty, lctx, slack)
  | Type _ -> failwith "infer_l Type"
  | Prod _ -> failwith "infer_l Prod"
  | Lolli _ -> failwith "infer_l Lolli"
  | Lambda _ -> failwith "infer_l Lambda"
  | App (t1, t2) -> (
    let t1, lctx, slack1 = infer_l ictx lctx t1 in
    match whnf t1 with
    | Lolli (ty1, ty2) ->
      let lctx, slack2 = check_l ictx lctx t2 ty1 in
      (ty2, lctx, slack1 || slack2)
    | Prod (ty, b) ->
      let () = check_i ictx t2 ty in
      (subst b t2, lctx, slack1)
    | _ -> failwith "infer_l App")
  | LetIn (t, b) -> (
    try 
      let x, b = unbind b in
      let ty, lctx, slack1 = infer_l ictx lctx t in
      let () = check_i ictx ty (Type L) in
      let lctx = add x ty lctx in
      let ty, lctx, slack2 = infer_l ictx lctx b in
      let () = assert_msg (not_in x lctx || slack2) "infer_l F_elim" in
      (ty, lctx, slack1 || slack2)
    with _ -> 
      let ty = infer_i ictx t in
      let () = check_i ictx ty (Type I) in
      infer_l ictx lctx (subst b t))
  | Eq _ -> failwith "infer_l Eq"
  | Refl _ -> failwith "infer_l Refl"
  | Ind _ -> failwith "infer_l Ind"
  | G _ -> failwith "infer_l G"
  | G_intro _ -> failwith "infer_l G_intro"
  | G_elim t -> (
    let ty = infer_i ictx t in
    match whnf ty with
    | G ty -> (ty, lctx, false)
    | _ -> failwith "infer_l G_elim")
  | F _ -> failwith "infer_l F"
  | F_intro _ -> failwith "infer_l F_intro"
  | F_elim (t, mb) -> (
    let t, lctx, slack1 = infer_l ictx lctx t in
    match whnf t with
    | F (t, b) ->
      let mx, mb = unmbind mb in
      let x1, x2 = mx.(0), mx.(1) in
      let b = subst b (Var x1) in
      let ictx = add x1 t ictx in
      let lctx = add x2 b lctx in
      let ty, lctx, slack2 = infer_l ictx lctx mb in
      let () = assert_msg (not_in x2 lctx || slack2) "infer_l F_elim" in
      (ty, lctx, slack1 || slack2)
    | _ -> failwith "infer_l F_elim")
  | Sum _ -> failwith "infer_l Sum"
  | Tensor _ -> failwith "infer_l Tensor"
  | And _ -> failwith "infer_l And"
  | Pair _ -> failwith "infer_l Pair"
  | Proj1 t -> (
    let t, lctx, slack = infer_l ictx lctx t in
    match whnf t with
    | And (ty, _) -> (ty, lctx, slack)
    | _ -> failwith "infer_l Proj1")
  | Proj2 t -> (
    let t, lctx, slack = infer_l ictx lctx t in
    match whnf t with
    | And (_, ty) -> (ty, lctx, slack)
    | _ -> failwith "infer_l Proj2")
  | Tensor_elim (t, mb) -> (
    let t, lctx, slack1 = infer_l ictx lctx t in
    match whnf t with
    | Tensor (ty1, ty2) ->
      let mx, b = unmbind mb in
      let x1, x2 = mx.(0), mx.(1) in
      let lctx = add x1 ty1 lctx in
      let lctx = add x2 ty2 lctx in
      let ty, lctx, slack2 = infer_l ictx lctx b in
      let () = assert_msg (not_in x1 lctx || slack2) "infer_l Tensor_elim" in
      let () = assert_msg (not_in x2 lctx || slack2) "infer_l Tensor_elim" in
      (ty, lctx, slack1 || slack2)
    | _ -> failwith "infer_l Tensor_elim")
  | Unit _ -> failwith "infer_l Unit"
  | True -> failwith "infer_l True"
  | U -> failwith "infer_l U"
  | Unit_elim (t1, t2) -> (
    let t1, lctx, slack1 = infer_l ictx lctx t1 in
    match whnf t1 with
    | Unit L -> 
      let t2, lctx, slack2 = infer_l ictx lctx t2 in
      (t2, lctx, slack1 || slack2)
    | _ -> failwith "infer_l Unit_elim")
  | Axiom (ty, b) ->
    let x, b = unbind b in
    let () = check_i ictx ty (Type L) in
    let lctx = add x ty lctx in
    let ty, lctx, slack = infer_l ictx lctx b in
    let () = assert_msg (not_in x lctx || slack) "infer_l Axiom" in
    (ty, lctx, slack)

and check_l ictx lctx t ty =
  let () = debug ictx ~lctx:lctx t ~ty:ty () in
  match t with
  | Lambda b -> (
    let () = check_i ictx ty (Type L) in
    match whnf ty with
    | Lolli (ty1, ty2) ->
      let x, b = unbind b in
      let lctx = add x ty1 lctx in
      let lctx, slack = check_l ictx lctx b ty2 in
      let () = assert_msg (not_in x lctx || slack) "check_l Lambda" in
      let lctx = remove x lctx in
      (lctx, slack)
    | Prod (ty, b') ->
      let x, b, b' = unbind2 b b' in
      let ictx = add x ty ictx in
      check_l ictx lctx b b'
    | _ -> failwith "check_l Lambda")
  | F_intro (t1, t2) -> (
    let () = check_i ictx ty (Type L) in
    match whnf ty with
    | F (ty, b) ->
      let () = check_i ictx t1 ty in
      check_l ictx lctx t2 (subst b t1)
    | _ -> failwith "check_l F_intro")
  | Pair (t1, t2) -> (
    let () = check_i ictx ty (Type L) in
    match whnf ty with
    | Tensor (ty1, ty2) ->
      let lctx, slack1 = check_l ictx lctx t1 ty1 in
      let lctx, slack2 = check_l ictx lctx t2 ty2 in
      (lctx, slack1 || slack2)
    | And (ty1, ty2) -> (
      let lctx1, slack1 = check_l ictx lctx t1 ty1 in
      let lctx2, slack2 = check_l ictx lctx t2 ty2 in
      let lctx = intersect lctx1 lctx2 in
      match slack1, slack2 with
      | false, false ->
        let () = assert_msg (Context.equal lctx1 lctx2) "check_l Pair" in
        (lctx, false)
      | false, true ->
        let () = assert_msg (is_subset lctx1 lctx2) "check_l Pair" in
        (lctx, false)
      | true, false ->
        let () = assert_msg (is_subset lctx2 lctx1) "check_l Pair" in
        (lctx, false)
      | true, true ->
        (lctx, true))
    | _ -> failwith "check_l Pair")
  | U -> (
    let () = check_i ictx ty (Type L) in
    match whnf ty with
    | Unit L -> (ictx, false)
    | True -> (ictx, true)
    | _ -> failwith "check_l U")
  | _ ->
    let t, lctx, slack = infer_l ictx lctx t in
    let () = assert_msg (equal t ty)
      (Format.asprintf "\ncheck_l\n t  := %a\n ty := %a" pp t pp ty) 
    in
    (lctx, slack)