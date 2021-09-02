open Bindlib
open Names
open Surface


type vctx = (t var * t) list
type mctx = (t M.t * t) list

type u_prob = vctx * t * t * t * t

let pp_m fmt mctx =
  List.iter
    (fun (m, ty) ->
      Format.fprintf fmt "%a : %a@." M.pp m pp ty) mctx

let pp_u fmt ps =
  List.iter 
    (fun (_, t1, t1_ty, t2, t2_ty) -> 
      Format.fprintf fmt "%a : %a === %a : %a@." 
        pp t1 pp t1_ty pp t2 pp t2_ty) 
    ps

let rec lookup_v vctx x =
  match vctx with
  | (y, t) :: vctx ->
    if eq_vars x y 
    then t
    else lookup_v vctx x
  | [] -> failwith "lookup_v"

let add_v vctx x ty = (x, ty) :: vctx

let rec lookup_m mctx x =
  match mctx with
  | (y, t) :: mctx ->
    if M.equal x y
    then t
    else lookup_m mctx x
  | [] -> failwith "lookup_m"

let add_m mctx m ty = (m, ty) :: mctx

let strip vctx =
  List.map (fun (x, _) -> (V x)) vctx

let rec elab mctx vctx t ty =
  match t with
  | V x ->
    let m = M.mk "m" in
    let m_ty = unbox (_Prod' vctx ty) in
    let m_app = unbox (_App' (M m) (strip vctx)) in
    let mctx = add_m mctx m m_ty in
    let t_ty = lookup_v vctx x in
    let c = (vctx, t, t_ty, m_app, ty) :: [] in
    (mctx, m_app, c)
  | M x ->
    let m = M.mk "m" in
    let m_ty = unbox (_Prod' vctx ty) in
    let m_app = unbox (_App' (M m) (strip vctx)) in
    let mctx = add_m mctx m m_ty in
    let t_ty = lookup_m mctx x in
    let c = (vctx, t, t_ty, m_app, ty) :: [] in
    (mctx, m_app, c)
  | Type ->
    let m = M.mk "m" in
    let m_ty = unbox (_Prod' vctx ty) in
    let m_app = unbox (_App' (M m) (strip vctx)) in
    let mctx = add_m mctx m m_ty in
    let c = (vctx, Type, Type, m_app, ty) :: [] in
    (mctx, m_app, c)
  | Prod (a, b) ->
    let x, b = unbind b in
    let mctx, a', a_c = elab mctx vctx a Type in
    let mctx, b', b_c = elab mctx (add_v vctx x a') b Type in
    let m = M.mk "m" in
    let m_ty = unbox (_Prod' vctx ty) in
    let m_app = unbox (_App' (M m) (strip vctx)) in
    let mctx = add_m mctx m m_ty in
    let t = unbox (_Prod (lift a') (bind_var x (lift b'))) in
    let c = (vctx, t, Type, m_app, ty) :: a_c @ b_c in
    (mctx, m_app, c)
  | Lambda b ->
    let x, ub = unbind b in
    let m1 = M.mk "m1" in
    let m1_ty = unbox (_Prod' vctx Type) in
    let m1_app = _App' (M m1) (strip vctx) in
    let vctx' = (add_v vctx x (M m1)) in
    let m2 = M.mk "m2" in
    let m2_ty = unbox (_Prod' vctx' Type) in
    let m2_app = _App' (M m2) (strip vctx') in
    let mctx = add_m mctx m1 m1_ty in
    let mctx = add_m mctx m2 m2_ty in
    let ub_ty = unbox m2_app in
    let mctx, u, c = elab mctx vctx' ub ub_ty in
    let m = M.mk "m" in
    let m_ty = unbox (_Prod' vctx ty) in
    let m_app = unbox (_App' (M m) (strip vctx)) in
    let mctx = add_m mctx m m_ty in
    let t = unbox (_Lambda (bind_var x (lift u))) in
    let t_ty = unbox (_Prod m1_app (bind_var x m2_app)) in
    let c = (vctx, t, t_ty, m_app, ty) :: c in
    (mctx, m_app, c)
  | App (t1, t2) ->
    let x = mk "x" in
    let m1 = M.mk "m1" in
    let m1_ty = unbox (_Prod' vctx Type) in
    let m1_app = _App' (M m1) (strip vctx) in
    let mctx = add_m mctx m1 m1_ty in
    let vctx' = add_v vctx x (M m1) in
    let m2 = M.mk "m2" in
    let m2_ty = unbox (_Prod' vctx' Type) in
    let m2_app = _App' (M m2) (strip vctx') in
    let mctx = add_m mctx m2 m2_ty in
    let t1_b = bind_var x m2_app in
    let t1_ty = unbox (_Prod m1_app t1_b) in
    let t2_ty = unbox m2_app in
    let mctx, t1, t1_c = elab mctx vctx t1 t1_ty in
    let mctx, t2, t2_c = elab mctx vctx t2 t2_ty in
    let m = M.mk "m" in
    let m_ty = unbox (_Prod' vctx ty) in
    let m_app = unbox (_App' (M m) (strip vctx)) in
    let mctx = add_m mctx m m_ty in
    let t = App (t1, t2) in
    let t_ty = subst (unbox t1_b) t2 in
    let c = (vctx, t, t_ty, m_app, ty) :: t1_c @ t2_c in
    (mctx, m_app, c)
