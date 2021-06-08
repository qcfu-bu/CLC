open Bindlib
open Rig

type t = 
  | Var    of t var
  | Ann    of t * ty
  | Type   of rig
  | Prod   of rig * ty * (ty, ty) binder
  | Lambda of rig * (t, t) binder
  | App    of t * t
  | LetIn  of t * (t, t) binder
  | Axiom  of ty * (ty, t) binder

and ty = t

type tvar = t var

let mk s = new_var (fun x -> Var x) s
let __ = mk "_"

let _Var = box_var
let _Ann = box_apply2 (fun t ty -> Ann (t, ty))
let _Type r = box (Type r)
let _Prod r = box_apply2 (fun ty b -> Prod (r, ty, b))
let _Lambda r = box_apply (fun b -> Lambda (r, b))
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))
let _LetIn = box_apply2 (fun t1 t2 -> LetIn (t1, t2))
let _Axiom = box_apply2 (fun ty t -> Axiom (ty, t))

let rec pp fmt = function
  | Var x -> 
    Format.fprintf fmt "%s" (name_of x)
  | Ann (s, t) -> 
    Format.fprintf fmt "(%a : %a)" pp s pp t
  | Type r -> Format.fprintf fmt "Type(%a)" Rig.pp r
  | Prod (q, t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[forall (%s :%a@;<1 2>%a),@]@;<1 2>%a@]"
      (name_of x) Rig.pp q pp t pp b
  | Lambda (r, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "@[fun %s %a>@;<1 2>%a@]"
      (name_of x) Rig.pp r pp b
  | App (s, t) ->
    Format.fprintf fmt "(%a) %a" pp s pp t
  | LetIn (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[let %s : :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x) pp t pp b
  | Axiom (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[axiom %s :@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x) pp t pp b