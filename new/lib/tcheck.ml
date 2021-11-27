open Bindlib
open Format
open Util
open Names
open Terms
open Context
open Equality

let rec infer_sort v_ctx id_ctx ty =
  let t, _, ctx = infer v_ctx id_ctx ty in
  match whnf t with
  | Sort srt ->
    assert_msg (VarMap.is_empty ctx) 
      "non-clean context for sort"; srt
  | _ -> 
    failwith 
      (asprintf "infer_sort(ty := %a; sort := %a)"
        Terms.pp ty Terms.pp t)

and infer v_ctx id_ctx t =
  match t with
  (* functional *)
  | Var x -> (
    let ty, srt =
      try find x v_ctx
      with e -> printf "%a" Context.pp v_ctx; raise e
    in
    match srt with
    | U -> (ty, U, VarMap.empty)
    | L -> (ty, L, VarMap.singleton x ty))
  | Sort srt -> (
    match srt with
    | U -> (Sort U, U, VarMap.empty)
    | L -> (Sort U, U, VarMap.empty))
  | Arrow (ty, b) -> (
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let _ = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
    (Sort U, U, VarMap.empty))
  | Lolli (ty, b) -> (
    let x, ub = unbind b in
    let srt = infer_sort v_ctx id_ctx ty in
    let _ = infer_sort (VarMap.add x (ty, srt) v_ctx) id_ctx ub in
    (Sort L, U, VarMap.empty))
  (* inductive *)
  (* inference *)
  | Meta _ -> failwith "infer Meta"
  | Ann (t, ty) -> (
    let srt = infer_sort v_ctx id_ctx ty in
    match t with
    | LetIn (t, b) ->
      let x, ub = unbind b in
      let b = unbox @@ bind_var x @@ lift @@ Ann (ub, ty) in
      let ctx = check v_ctx id_ctx (LetIn (t, b)) ty srt in
      (ty, srt, ctx)
    | _ ->
      let ctx = check v_ctx id_ctx t ty srt in
      (ty, srt, ctx))
  (* axiom *)
  | _ -> failwith "unimplemented"

and check v_ctx id_ctx t ty srt = 
  failwith "unimplemented"