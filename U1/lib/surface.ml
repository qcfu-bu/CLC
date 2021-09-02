open Bindlib
open Names

type t =
  | V      of tvar
  | M      of mvar
  | Type
  | Prod   of t * (t, t) binder
  | Lambda of (t, t) binder
  | App    of t * t

and tvar = t var
and mvar = t M.t

let mk = new_var (fun x -> V x)
let __ = mk "_"

let _V = box_var
let _M m = box (M m)
let _Type = box Type
let _Prod = box_apply2 (fun ty b -> Prod (ty, b))
let _Arrow ty1 ty2 = _Prod ty1 (bind_var __ ty2)
let _Lambda = box_apply (fun b -> Lambda b)
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))

let rec lift = function
  | V x -> _V x
  | M m -> _M m
  | Type -> _Type
  | Prod (ty, b) -> _Prod (lift ty) (box_binder lift b)
  | Lambda b -> _Lambda (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)

let _App' t ts = 
  List.fold_left (fun acc t -> 
    let t = lift t in
    _App acc t) (lift t) ts
let _Prod' ts t = 
  List.fold_right 
    (fun (x, ty) acc -> 
      let ty = lift ty in
      _Prod ty (bind_var x acc)) ts (lift t)

let pp_v fmt x = 
  Format.fprintf fmt "%s_%d" (name_of x) (uid_of x)

let rec pp fmt = function
  | V x -> 
    Format.fprintf fmt "%a" pp_v x
  | M m ->
    Format.fprintf fmt "%a" M.pp m
  | Type ->
    Format.fprintf fmt "Type"
  | Prod (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then Format.fprintf fmt "@[(%a -> %a)@]" pp ty pp b
    else Format.fprintf fmt "@[(%a : %a) -> %a@]"
      pp_v x pp ty pp b
  | Lambda b ->
    let x, t = unbind b in
    Format.fprintf fmt "@[(\\%a -> %a)@]" pp_v x pp t
  | App (t1, t2) -> 
    Format.fprintf fmt "@[(%a (%a))@]" pp t1 pp t2

let rec spine = function
  | App (t1, t2) ->
    let h, sp = spine t1 in
    (h, sp @ [t2])
  | h -> (h, [])

let rec aeq t1 t2 =
  match t1, t2 with
  | V x1, V x2 -> eq_vars x1 x2
  | M m1, M m2 -> M.equal m1 m2
  | Type, Type -> true
  | Prod (ty1, b1), Prod (ty2, b2) ->
    aeq ty1 ty2 && eq_binder aeq b1 b2
  | Lambda b1, Lambda b2 ->
    eq_binder aeq b1 b2
  | App (t11, t12), App (t21, t22) ->
    aeq t11 t21 && aeq t12 t22
  | _ -> false

let rec nf t =
  match t with
  | V _ -> t
  | M m -> (
    match M.get m with
    | Some t -> nf t 
    | None -> t)
  | Type -> t
  | Prod (ty, b) ->
    let ty = nf ty in
    let x, t = unbind b in
    let b = unbox (bind_var x (lift (nf t))) in
    Prod (ty, b)
  | Lambda b ->
    let x, t = unbind b in
    let b = unbox (bind_var x (lift (nf t))) in
    Lambda b
  | App (t1, t2) -> (
    let t1 = nf t1 in
    let t2 = nf t2 in
    match t1, t2 with
    | Lambda b, _ -> nf (subst b t2)
    | _ -> App (t1, t2))
  
let rec equal t1 t2 ty =
  if aeq t1 t2 then true
  else
    let t1 = nf t1 in
    let t2 = nf t2 in
    let ty = nf ty in
    match ty with
    | Prod (_, b) ->
      let x, ty = unbind b in
      let t1 = nf (App (t1, V x)) in
      let t2 = nf (App (t2, V x)) in
      equal t1 t2 ty
    | _ -> aeq t1 t2