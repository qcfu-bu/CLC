open Bindlib

type t =
  | Var    of t var
  | Ann    of t * ty
  | Type
  | Linear
  | TyProd of ty * (t, ty) binder
  | LnProd of ty * (t, ty) binder
  | Lambda of (t, t) binder
  | App    of t * t
  | LetIn  of t * (t, t) binder
  | Axiom  of ty * (ty, t) binder

and ty = t

type tvar = t var

let mk = new_var (fun x -> Var x)
let __ = mk "_"

let _Var = box_var
let _Ann = box_apply2 (fun t ty -> Ann (t, ty))
let _Type = box Type
let _Linear = box Linear
let _TyProd = box_apply2 (fun ty b -> TyProd (ty, b))
let _LnProd = box_apply2 (fun ty b -> LnProd (ty, b))
let _Lambda = box_apply (fun t -> Lambda t)
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))
let _LetIn = box_apply2 (fun t b -> LetIn (t ,b))
let _Axiom = box_apply2 (fun ty b -> Axiom (ty, b))

let rec lift = function
  | Var x -> _Var x
  | Ann (t, ty) -> _Ann (lift t) (lift ty)
  | Type -> _Type
  | Linear -> _Linear
  | TyProd (ty, b) -> _TyProd (lift ty) (box_binder lift b)
  | LnProd (ty, b) -> _LnProd (lift ty) (box_binder lift b)
  | Lambda b -> _Lambda (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)
  | LetIn (t, b) -> _LetIn (lift t) (box_binder lift b)
  | Axiom (ty, b) -> _Axiom (lift ty) (box_binder lift b)

let rec pp fmt = function
  | Var x -> 
    Format.fprintf fmt "%s" (name_of x)
  | Ann (s, t) -> 
    Format.fprintf fmt "(%a : %a)" pp s pp t
  | Type -> Format.fprintf fmt "Type"
  | Linear -> Format.fprintf fmt "Linear"
  | TyProd (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[(%s :@;<1 2>%a)->@]@;<1 2>%a@]"
      (name_of x) pp t pp b
  | LnProd (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[(%s :@;<1 2>%a)>>@]@;<1 2>%a@]"
      (name_of x) pp t pp b
  | Lambda b ->
    let x, b = unbind b in
    Format.fprintf fmt "@[fun %s =>@;<1 2>%a@]"
      (name_of x) pp b
  | App (s, t) ->
    Format.fprintf fmt "(%a) %a" pp s pp t
  | LetIn (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[let %s :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x) pp t pp b
  | Axiom (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[axiom %s :@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x) pp t pp b