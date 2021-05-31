open Bindlib

type term =
  | Var of term var
  | Type
  | Prod   of int * term * (term, term) binder
  | Lambda of int * term * (term, term) binder
  | Fix    of int * term * (term, term) binder
  | LetIn  of int * term * term * (term, term) binder
  | App    of term * term
  | Magic

type tvar = term var

let _Var = box_var

let _Type = box Type

let _Prod q = box_apply2 (fun t b -> Prod (q, t, b))

let _Lambda q = box_apply2 (fun t b -> Lambda (q, t, b))

let _Fix q = box_apply2 (fun t b -> Fix (q, t, b))

let _LetIn q = box_apply3 (fun t1 t2 b -> LetIn (q, t1, t2, b))

let _App = box_apply2 (fun t1 t2 -> App (t1, t2))

let _Magic = box Magic

let rec lift = function
  | Var x -> _Var x
  | Type  -> _Type
  | Prod (q, t, b) -> 
    _Prod q (lift t) (box_binder lift b)
  | Lambda (q, t, b) ->
    _Lambda q (lift t) (box_binder lift b)
  | Fix (q, t, b) ->
    _Fix q (lift t) (box_binder lift b)
  | LetIn (q, t1, t2, b) ->
    _LetIn q (lift t1) (lift t2) (box_binder lift b)
  | App (t1, t2) ->
    _App (lift t1) (lift t2)
  | Magic -> _Magic

let rec pp fmt = function
  | Var x -> Format.fprintf fmt "%s" (name_of x)
  | Type -> Format.fprintf fmt "Type"
  | Prod (q, t, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "forall (%s :%d %a), %a"
      (name_of x) q pp t pp b
  | Lambda (q, t, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "fun (%s :%d %a) => %a"
      (name_of x) q pp t pp b
  | Fix (q, t, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "fix (%s :%d %a) := %a"
      (name_of x) q pp t pp b
  | LetIn (q, t1, t2, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "let %s :%d %a := %a in %a"
      (name_of x) q pp t1 pp t2 pp b
  | App (t1, t2) ->
    Format.fprintf fmt "(%a) %a" pp t1 pp t2
  | Magic -> 
    Format.fprintf fmt "??"