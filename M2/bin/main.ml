open Bindlib
open M2
open Terms
open Context
open Typec

let f = new_var (fun x -> Var x) "f"
let x = new_var (fun x -> Var x) "x"
let y = new_var (fun x -> Var x) "y"

let ty = _Prod 1 _Type (bind_var y (_Type))
let t = 
  _Fix 1 ty (bind_var f
    (_Lambda 1 _Type (bind_var x (_App (_Var f) (_Var x)))))

let d = _Lambda 1 ty (bind_var x _Type)

let ty = unbox ty

let t = unbox t

let d = unbox d

let _ = 
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

let _ = Norm.cbn (App (d, App (t, Magic)))