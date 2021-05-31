open Bindlib
open Rig

type term =
  | Var of term var
  | Ann of term * term
  | Type
  | Prod   of rig * term * (term, term) binder
  | Lambda of (term, term) binder
  | Fix    of (term, term) binder
  | App    of term * term

type tvar = term var

let _Var = box_var
let _Ann = box_apply2 (fun s t -> Ann (s, t))
let _Type = box Type
let _Prod q = box_apply2 (fun t b -> Prod (q, t, b))
let _Lambda = box_apply (fun b -> Lambda b)
let _Fix = box_apply (fun b -> Fix b)
let _App = box_apply2 (fun s t -> App (s, t))

let rec lift = function
  | Var x -> _Var x
  | Ann (s, t) -> _Ann (lift s) (lift t)
  | Type -> _Type
  | Prod (q, t, b) ->
    _Prod q (lift t) (box_binder lift b)
  | Lambda b -> _Lambda (box_binder lift b)
  | Fix b -> _Fix (box_binder lift b)
  | App (s, t) -> _App (lift s) (lift t)

let rec pp fmt = function
  | Var x -> Format.fprintf fmt "%s" (name_of x)
  | Ann (s, t) -> Format.fprintf fmt "(%a : %a)" pp s pp t
  | Type -> Format.fprintf fmt "Type"
  | Prod (q, t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "forall (%s :%a %a), %a"
      (name_of x) Rig.pp q  pp t pp b
  | Lambda b ->
    let x, b = unbind b in
    Format.fprintf fmt "fun %s => %a"
      (name_of x) pp b
  | Fix b ->
    let x, b = unbind b in
    Format.fprintf fmt "fix %s := %a"
      (name_of x) pp b
  | App (s, t) ->
    Format.fprintf fmt "(%a) %a" pp s pp t