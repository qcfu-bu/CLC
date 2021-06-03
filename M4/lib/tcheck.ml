open Bindlib
open Terms
open Norms
open Context
open Equality

let assert_msg cond msg = 
  if cond then ()
  else failwith msg

let rec infer_i ictx = function
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
  | G ty ->
    let () = check_i ictx ty (Type L) in
    Type I
  | G_intro t ->
    let ty, _ = infer_l ictx empty t in
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

and check_i ictx t ty =
  match t with
  | Lambda (m, t) -> (
    let () = check_i ictx ty (Type I) in
    match m, whnf ty with
    | I, Prod (ty, b) ->
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
    assert_msg (equal t ty) "check_i"

and infer_l ictx lctx = function
  | Var x ->
    let ty = find x lctx in
    let lctx = remove x lctx in
    (ty, lctx)
  | Ann (t, ty) ->
    let lctx = check_l ictx lctx t ty in
    (ty, lctx)
  | Type _ -> failwith "infer_l Type"
  | Prod _ -> failwith "infer_l Prod"
  | Lolli _ -> failwith "infer_l Lolli"
  | Lambda _ -> failwith "infer_l Lambda"
  | App (t1, t2) -> (
    let t1, lctx = infer_l ictx lctx t1 in
    match whnf t1 with
    | Lolli (ty1, ty2) ->
      let lctx = check_l ictx lctx t2 ty1 in
      (ty2, lctx)
    | Prod (ty, b) ->
      let () = check_i ictx t2 ty in
      (subst b t2, lctx)
    | _ -> failwith "infer_l App")
  | G _ -> failwith "infer_l G"
  | G_intro _ -> failwith "infer_l G_intro"
  | G_elim t -> (
    let ty = infer_i ictx t in
    match whnf ty with
    | G ty -> (ty, lctx)
    | _ -> failwith "infer_l G_elim")
  | F _ -> failwith "infer_l F"
  | F_intro _ -> failwith "infer_l F_intro"
  | F_elim (t, mb) -> (
    let t, lctx = infer_l ictx lctx t in
    match whnf t with
    | F (t, b) ->
      let mx, mb = unmbind mb in
      let x1, x2 = mx.(0), mx.(1) in
      let b = subst b (Var x1) in
      let ictx = add x1 t ictx in
      let lctx = add x2 b lctx in
      let ty, lctx = infer_l ictx lctx mb in
      let () = assert_msg (not (contains x2 lctx)) "infer_l F_elim" in
      (ty, lctx)
    | _ -> failwith "infer_l F_elim")
  | Sum _ -> failwith "infer_l Sum"
  | Tensor _ -> failwith "infer_l Tensor"
  | And _ -> failwith "infer_l And"
  | Pair _ -> failwith "infer_l Pair"
  | Proj1 t -> (
    let t, lctx = infer_l ictx lctx t in
    match whnf t with
    | And (ty, _) -> (ty, lctx)
    | _ -> failwith "infer_l Proj1")
  | Proj2 t -> (
    let t, lctx = infer_l ictx lctx t in
    match whnf t with
    | And (_, ty) -> (ty, lctx)
    | _ -> failwith "infer_l Proj2")
  | Tensor_elim (t, mb) -> (
    let t, lctx = infer_l lctx ictx t in
    match whnf t with
    | Tensor (ty1, ty2) ->
      let mx, b = unmbind mb in
      let x1, x2 = mx.(0), mx.(1) in
      let lctx = add x1 ty1 lctx in
      let lctx = add x2 ty2 lctx in
      let ty, lctx = infer_l ictx lctx b in
      let () = assert_msg (not (contains x1 lctx)) "infer_l Tensor_elim" in
      let () = assert_msg (not (contains x2 lctx)) "infer_l Tensor_elim" in
      (ty, lctx)
    | _ -> failwith "infer_l Tensor_elim")
  | Unit _ -> failwith "infer_l Unit"
  | True -> failwith "infer_l True"
  | U -> failwith "infer_l U"
  | Unit_elim (t1, t2) -> (
    let t1, lctx = infer_l ictx lctx t1 in
    match whnf t1 with
    | Unit L -> infer_l ictx lctx t2
    | _ -> failwith "infer_l Unit_elim")

and check_l ictx lctx t ty =
  match t with
  | Lambda (m, b) -> (
    let () = check_i ictx ty (Type I) in
    match m, whnf ty with
    | I, Lolli (ty1, ty2) ->
      let x, b = unbind b in
      let lctx = add x ty1 lctx in
      let lctx = check_l ictx lctx b ty2 in
      let () = assert_msg (not (contains x lctx)) "check_l Lambda" in
      lctx
    | L, Prod (ty, b') ->
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
      let lctx = check_l ictx lctx t1 ty1 in
      let lctx = check_l ictx lctx t2 ty2 in
      lctx
    | And (ty1, ty2) ->
      let lctx1 = check_l ictx lctx t1 ty1 in
      let lctx2 = check_l ictx lctx t2 ty2 in
      let () = assert_msg (Context.equal lctx1 lctx2) "check_l Pair" in
      lctx1
    | _ -> failwith "check_l Pair")
  | U -> (
    let () = check_i ictx ty (Type L) in
    match whnf ty with
    | Unit L -> ictx
    | True -> ictx
    | _ -> failwith "check_l U")
  | _ ->
    let t, lctx = infer_l ictx lctx t in
    let () = assert_msg (equal t ty) "check_l" in
    lctx