open Bindlib
open Rig

type term =
  | Var    of term var
  | AnnTy  of term * term
  | AnnVr  of term * term var
  | Type
  | Prod   of rig * term * (term, term) binder
  | Lambda of (term, term) binder
  | Fix    of (term, term) binder
  | App    of term * term
  | LetIn  of rig * term * (term, term) binder

type tvar = term var

let __ = new_var (fun x -> Var x) "_"
let mk = new_var (fun x -> Var x)

let _Var = box_var
let _AnnTy = box_apply2 (fun s t -> AnnTy (s, t))
let _AnnVr t x = box_apply (fun t -> AnnVr (t, x)) t
let _Type = box Type
let _Prod q = box_apply2 (fun t b -> Prod (q, t, b))
let _Lambda = box_apply (fun b -> Lambda b)
let _Fix = box_apply (fun b -> Fix b)
let _App = box_apply2 (fun s t -> App (s, t))
let _LetIn q = box_apply2 (fun t b -> LetIn (q, t, b))

let rec lift = function
  | Var x -> _Var x
  | AnnTy (s, t) -> _AnnTy (lift s) (lift t)
  | AnnVr (t, x) -> _AnnVr (lift t) x
  | Type -> _Type
  | Prod (q, t, b) ->
    _Prod q (lift t) (box_binder lift b)
  | Lambda b -> _Lambda (box_binder lift b)
  | Fix b -> _Fix (box_binder lift b)
  | App (s, t) -> _App (lift s) (lift t)
  | LetIn (q, t, b) ->
    _LetIn q (lift t) (box_binder lift b)

let rec pp fmt = function
  | Var x -> 
    Format.fprintf fmt "%s" (name_of x)
  | AnnTy (s, t) -> 
    Format.fprintf fmt "(%a : %a)" pp s pp t
  | AnnVr (t, x) -> 
    Format.fprintf fmt "(%a @ %s)" pp t (name_of x)
  | Type -> Format.fprintf fmt "Type"
  | Prod (q, t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "forall (%s :%a %a), %a"
      (name_of x) Rig.pp q pp t pp b
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
  | LetIn (q, t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "let %s :%a := %a in %a"
      (name_of x) Rig.pp q pp t pp b