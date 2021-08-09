open Bindlib
open Format

type ty =
  | Const of string
  | Fun of ty * ty

let fun' tys ty = 
  List.fold_right (fun ty acc -> Fun (ty, acc)) tys ty

module M : sig
  type t
  val mk : string -> ty -> t
  val eq : t -> t -> bool
  val ty : t -> ty
  val pp : formatter -> t -> unit
end =
struct
  type t = string * ty * int
  let stamp = ref 0
  let mk s ty = 
    let id = !stamp in
    incr stamp;
    (s, ty, id)
  let eq m1 m2 =
    let (_, _, id1) = m1 in
    let (_, _, id2) = m2 in
    id1 = id2
  let ty (_, ty, _) = ty
  let pp fmt (s, _, id) =
    fprintf fmt "?%s_%d" s id
end

module C : sig
  type t
  val mk : string -> ty -> t
  val eq : t -> t -> bool
  val ty : t -> ty
  val pp : formatter -> t -> unit
end =
struct
  type t = string * ty * int
  let stamp = ref 0
  let mk s ty =
    let id = !stamp in
    incr stamp;
    (s, ty, id)
  let eq c1 c2 =
    let (_, _, id1) = c1 in
    let (_, _, id2) = c2 in
    id1 = id2 
  let ty (_, ty, _) = ty
  let pp fmt (s, _, id) =
    fprintf fmt "$%s_%d" s id
end

type te = 
  | V of tvar
  | M of M.t
  | C of C.t
  | Lambda of ty * (te, te) binder
  | App    of te * te

and tvar = te var

let mk = new_var (fun x -> V x)
let _V = box_var
let _M m = box (M m)
let _C c = box (C c)
let _Lambda ty = box_apply (fun b -> Lambda (ty, b))
let rec _Lambda' xs t = 
  match xs with 
  | (x, ty) :: xs ->
    let t = _Lambda' xs t in
    _Lambda ty (bind_var x  t)
  | [] -> t
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))

let _App' h ls = box_apply2 (fun h ts ->
  List.fold_left (fun acc t -> App (acc, t)) h ts) h (box_list ls)

let rec lift = function
  | V x -> _V x
  | M x -> _M x
  | C x -> _C x
  | Lambda (ty, b) -> _Lambda ty (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)

let rec ty_eq ty1 ty2 = 
  match ty1, ty2 with
  | Const s1, Const s2 -> s1 = s2
  | Fun (ty11, ty12), Fun (ty21, ty22) ->
    ty_eq ty11 ty12 && ty_eq ty21 ty22
  | _ -> false

let rec te_aeq t1 t2 =
  match t1, t2 with
  | V x1, V x2 -> eq_vars x1 x2
  | M x1, M x2 -> M.eq x1 x2
  | C x1, C x2 -> C.eq x1 x2
  | Lambda (ty1, b1), Lambda (ty2, b2) ->
    let _, t1, t2 = unbind2 b1 b2 in
    te_aeq t1 t2 && ty_eq ty1 ty2
  | App (t11, t12), App (t21, t22) ->
    te_aeq t11 t21 && te_aeq t12 t22
  | _ -> false

let rec nf t = 
  match t with
  | V _ -> t
  | M _ -> t
  | Lambda (ty, b) ->
    let x, t = unbind b in
    let t = nf t in
    let b = unbox (bind_var x (lift t)) in
    Lambda (ty, b)
  | App (t1, t2) -> (
    let t1 = nf t1 in
    let t2 = nf t2 in
    match t1 with
    | Lambda (_, b) -> subst b t2
    | _ -> App (t1, t2))
  | C _ -> t

let rec te_eq t1 t2 =
  if te_aeq t1 t2 then true
  else
    let t1 = nf t1 in
    let t2 = nf t2 in
    match t1, t2 with
    | V x1, V x2 -> eq_vars x1 x2
    | M x1, M x2 -> M.eq x1 x2
    | C x1, C x2 -> C.eq x1 x2
    | Lambda (ty1, b1), Lambda (ty2, b2) ->
      let _, t1, t2 = unbind2 b1 b2 in
      te_eq t1 t2 && ty_eq ty1 ty2
    | App (t11, t12), App (t21, t22) ->
      te_eq t11 t21 && te_eq t12 t22
    | _ -> false

let rec msubst t m n =
  match t with
  | V _ -> t
  | M x ->
    if M.eq x m
    then n
    else t
  | C _ -> t
  | Lambda (ty, b) ->
    let x, t = unbind b in
    let t = msubst t m n in
    let b = unbox (bind_var x (lift t)) in
    Lambda (ty, b)
  | App (t1, t2) ->
    App (msubst t1 m n, msubst t2 m n)

let pp_v fmt x =
  fprintf fmt "%s#%d" (name_of x) (uid_of x)

let rec pp_ty fmt = function
  | Const c -> fprintf fmt "%s" c
  | Fun (ty1, ty2) -> fprintf fmt "%a -> %a" pp_ty ty1 pp_ty ty2

let rec pp fmt = function
  | V x -> fprintf fmt "%a" pp_v x
  | M x -> fprintf fmt "%a" M.pp x
  | C x -> fprintf fmt "%a" C.pp x
  | Lambda (ty, b) ->
    let x, t = unbind b in
    fprintf fmt "(\\%a : %a -> %a)" pp_v x pp_ty ty pp t
  | App (t1, t2) ->
    fprintf fmt "(%a (%a))" pp t1 pp t2