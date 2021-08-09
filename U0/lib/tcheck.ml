open Bindlib
open Terms

type vctx = (tvar * ty) list

let rec find_v ctx x =
  match ctx with
  | (v, ty) :: ctx ->
    if eq_vars v x
    then ty
    else find_v ctx x
  | _ -> failwith "find_v failed"

let rec infer vctx t =
  match t with
  | V x -> find_v vctx x
  | M x -> M.ty x
  | C x -> C.ty x
  | Lambda (ty1, b) -> 
    let x, t = unbind b in
    let vctx = (x, ty1) :: vctx in
    let ty2 = infer vctx t in
    Fun (ty1, ty2)
  | App (t1, t2) -> (
    let ty = infer vctx t1 in
    match ty with
    | Fun (ty1, ty) ->
      let ty2 = infer vctx t2 in
      if (ty_eq ty1 ty2) 
      then ty
      else failwith "infer app"
    | _ -> failwith "infer app")
