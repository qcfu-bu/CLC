open Ast
open Norm
module FMap = Map.Make (Var)

let ( let* ) x f = match x with Some x -> f x | None -> None

type context = (ty * int) FMap.t

let scale (ctx : context) (n : int) : context =
  FMap.map (fun (ty, q) -> ty, n * q) ctx
;;

let sum (ctx1 : context) (ctx2 : context) : context =
  FMap.merge
    (fun _ r1 r2 ->
      match r1, r2 with
      | Some (ty1, q1), Some (ty2, q2) ->
        if eq ty1 ty2 then Some (ty1, q1 + q2) else None
      | Some (ty1, q1), _ -> Some (ty1, q1)
      | _, Some (ty2, q2) -> Some (ty2, q2)
      | _ -> None)
    ctx1
    ctx2
;;

let contract (ctx : context) : context =
  FMap.filter (fun _ (_, q) -> q <> 0) ctx
;;

let rec tcheck (ctx : context) (t : term) (ty : ty) (q : int)
    : context option
  =
  let _ = Printf.printf "q(%d)\n" q in
  if not (q = 0 || q = 1)
  then None
  else (
    match t with
    | Var v ->
      let* ty', q' = FMap.find_opt v ctx in
      if eq ty ty' && q' >= q
      then (
        let ctx = scale ctx 0 in
        let* _ = tcheck ctx ty TT 0 in
        let ctx = FMap.add v (ty, q' - q) ctx in
        Some ctx)
      else None
    | TT -> if eq ty TT && q = 0 then Some ctx else None
    | Fun t ->
      if eq ty TT && q = 0
      then (
        let ctx' = scale ctx 0 in
        let* _ = tcheck ctx' t.arg_type TT 0 in
        let ctx' = FMap.add t.arg_name (t.arg_type, 0) ctx' in
        let* _ = tcheck ctx' t.out_type TT 0 in
        Some ctx)
      else None
    | Fix t ->
      let ty' =
        Fun
          { arg_name = t.arg_name
          ; arg_type = t.arg_type
          ; out_type = t.out_type
          ; quantity = t.quantity
          }
      in
      if eq ty ty'
      then (
        let ctx = FMap.add t.arg_name (t.arg_type, q * t.quantity) ctx in
        let ctx = FMap.add t.fun_name (ty, q) ctx in
        tcheck ctx t.bod_term t.out_type q)
      else None
    | App t ->
      let ty' =
        Fun
          { arg_name = t.arg_name
          ; arg_type = t.arg_type
          ; out_type = t.out_type
          ; quantity = t.quantity
          }
      in
      let q' = if t.quantity = 0 || q = 0 then 0 else 1 in
      let* ctx1 = tcheck ctx t.fun_term ty' q in
      let* ctx2 = tcheck ctx t.arg_term t.arg_type q' in
      let ty' = subst t.arg_name t.out_type t.arg_term in
      let _ = Format.printf "ty(%a)\n" pp ty in
      let _ = Format.printf "ty'(%a)\n" pp ty' in
      if eq ty ty'
      then (
        let _ = print_endline "ok" in
        let ctx' = sum ctx1 (scale ctx2 t.quantity) in
        let ctx' = sum ctx' (scale ctx (-t.quantity)) in
        if FMap.for_all (fun _ (_, q) -> q >= 0) ctx'
        then Some ctx'
        else None)
      else (
        let _ = print_endline "bad" in
        None)
    | Magic -> Some ctx)
;;

module Debug = struct
  let x = Var.mk "x"

  (* let ty = Fun { arg_name = x; arg_type = TT; out_type = TT; quantity = 0
     } *)
  let f = Var.mk "f"
  let x = Var.mk "x"
  let y = Var.mk "y"

  let fun_term =
    Fix
      { fun_name = f
      ; arg_name = x
      ; bod_term = Var x
      ; arg_type = TT
      ; out_type = TT
      ; quantity = 1
      }
  ;;

  let arg_term = TT

  let term =
    App
      { fun_term
      ; arg_term
      ; arg_name = y
      ; arg_type = TT
      ; out_type = TT
      ; quantity = 1
      }
  ;;

  let test () =
    match tcheck FMap.empty term TT 1 with
    | Some ctx -> FMap.is_empty (contract ctx)
    | None -> false
  ;;
end
