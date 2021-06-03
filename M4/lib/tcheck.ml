open Bindlib
open Terms
open Norms
open Context
open Equality

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
    try 
      let () = check_i ictx b (Type I) in
      Type I
    with _ ->
      let () = check_i ictx b (Type L) in
      Type L)
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
    let ty = infer_l ictx empty t in
    G ty
  | G_elim t -> failwith "infer_i G_elim"
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
    if not (equal (infer_i ictx t) ty)
    then failwith "check_i"

and infer_l ictx lctx t = failwith "??"

and check_l ictx lctx t ty = failwith "??"