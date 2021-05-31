open Bindlib
open M2
open Terms
open Context
open Typec

let f = new_var (fun x -> Var x) "f"
let g = new_var (fun x -> Var x) "g"
let x = new_var (fun x -> Var x) "x"
let y = new_var (fun x -> Var x) "y"

let ty1 = _Prod 0 _Type (bind_var x (_Type))
let t1 = 
  _Fix 0 ty1 (bind_var f
    (_Lambda 0 _Type (bind_var x (_App (_Var f) (_Var x)))))

let _ = 
  let ty1 = unbox ty1 in
  let t1 = unbox t1 in
  let ctx = check empty ty1 0 t1 in
  Format.printf "----------------------------\n";
  assert (is_zero ctx)

let ty2 = _Prod 0 ty1 (bind_var x (_Type))
let t2 =
  _Lambda 0 ty1 (bind_var x _Type)

let _ = 
  let ty2 = unbox ty2 in
  let t2 = unbox t2 in
  let ctx = check empty ty2 0 t2 in
  Format.printf "----------------------------\n";
  assert (is_zero ctx)

let t = 
  _LetIn 0 ty1 t1 (bind_var f (
    _LetIn 0 ty2 t2 (bind_var g
      (_App (_Var g) (_Var f)))))

let _ = 
  let t = unbox t in
  let ctx, ty = infer empty 0 t in
  Format.printf "ty := %a\n" pp ty;
  Format.printf "----------------------------\n";
  assert (is_zero ctx)

(* let d = _Lambda 1 ty (bind_var x _Type)

let ty = unbox ty

let t = unbox t

let d = unbox d *)


(* let _ = 
  let ctx = check empty ty 1 t in
  Format.printf "----------------------------\n";
  assert (is_zero ctx)

let _ = 
  let ctx = check empty Type 0 (App (t, Type)) in
  Format.printf "----------------------------\n";
  assert (is_zero ctx)

let _ = 
  let ctx = check empty Type 0 (App (d, t)) in
  Format.printf "----------------------------\n";
  assert (is_zero ctx)

let _ = Norm.cbn (App (d, App (t, Magic))) *)