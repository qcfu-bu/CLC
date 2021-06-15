open Bindlib

module Terms : sig
  type t =
    | Var of t var
    | Lambda of pbinder
    | Pair of t * t
    | App of t * t
  and p =
    | PVar of t var
    | PPair of p * p
  and pbinder

  val mk : string -> t var
  val __ : t var

  val bind_p : p -> t box -> pbinder box
  val unbind_p : pbinder -> p * t
  val subst_p : pbinder -> t -> t
  val eq_binder_p : (t -> t -> bool) -> pbinder -> pbinder -> bool

  val _Var : t var -> t box
  val _Lambda : pbinder box -> t box
  val _App : t box -> t box -> t box
  val _Pair : t box -> t box -> t box

  val lift : t -> t box
  val pp_p : Format.formatter -> p -> unit
  val pp : Format.formatter -> t -> unit
end
= 
struct
  type t =
    | Var of t var
    | Lambda of pbinder
    | Pair of t * t
    | App of t * t
  and p =
    | PVar of t var
    | PPair of p * p
  and p0 =
    | P0Rel
    | P0Pair of p0 * p0

  and pbinder = p0 * (t, t) mbinder

  let mk = new_var (fun x -> Var x)
  let __ = mk "_"

  let rec equal_p p1 p2 =
    match p1, p2 with
    | P0Rel, P0Rel -> true
    | P0Pair (p11, p12), P0Pair (p21, p22) ->
      equal_p p11 p21 && equal_p p12 p22
    | _ -> false

  let rec mt_of_pt p0 t =
    match p0, t with
    | P0Rel, _ -> [| t |]
    | P0Pair (p1, p2), Pair (t1, t2) ->
      let mt1 = mt_of_pt p1 t1 in
      let mt2 = mt_of_pt p2 t2 in
      Array.append mt1 mt2
    | _ -> failwith "mt_of_pt"

  let rec mvar_of_p = function
    | PVar x -> (P0Rel, [| x |])
    | PPair (p1, p2) ->
      let p1, m1 = mvar_of_p p1 in
      let p2, m2 = mvar_of_p p2 in
      (P0Pair (p1, p2), Array.append m1 m2)

  let rec p0_of_mvar p0 m = 
    match p0 with
    | P0Rel -> 
      let x = m.(0) in
      let m = Array.sub m 1 ((Array.length m) - 1) in
      (PVar x, m)
    | P0Pair (p1, p2) ->
      let p1, m = p0_of_mvar p1 m in
      let p2, m = p0_of_mvar p2 m in
      (PPair (p1, p2), m)

  let bind_p p (t : t box) : pbinder box =
    let p, m = mvar_of_p p in
    let mb = bind_mvar m t in
    box_apply (fun mb -> (p, mb)) mb

  let unbind_p (pb : pbinder) : p * t = 
    let p, mb = pb in
    let mx, t = unmbind mb in 
    let p, _ = p0_of_mvar p mx in
    (p, t)

  let subst_p (pb : pbinder) t : t =
    let p, mb = pb in
    let mt = mt_of_pt p t in
    msubst mb mt

  let box_binder_p f (pb : pbinder) =
    let p, mb = pb in
    let mb = box_mbinder f mb in
    box_apply (fun mb -> (p, mb)) mb

  let eq_binder_p f pb1 pb2 =
    let p1, mb1 = pb1 in
    let p2, mb2 = pb2 in
    equal_p p1 p2 && eq_mbinder f mb1 mb2

  let _Var = box_var
  let _Lambda = box_apply (fun b -> Lambda b)
  let _App = box_apply2 (fun t1 t2 -> App (t1, t2))
  let _Pair = box_apply2 (fun t1 t2 -> Pair (t1, t2))

  let rec lift = function
    | Var x -> _Var x
    | Lambda p -> _Lambda (box_binder_p lift p)
    | App (t1, t2) -> _App (lift t1) (lift t2)
    | Pair (t1, t2) -> _Pair (lift t1) (lift t2)

  let rec pp_p fmt = function
    | PVar x -> Format.fprintf fmt "%s" (name_of x)
    | PPair (p1, p2) ->
      Format.fprintf fmt "(%a, %a)" pp_p p1 pp_p p2

  let rec pp fmt = function
    | Var x -> Format.fprintf fmt "%s#%d" (name_of x) (uid_of x)
    | Lambda pb ->
      let p, b = unbind_p pb in
      Format.fprintf fmt "fun %a -> %a" pp_p p pp b
    | App (t1, t2) ->
      Format.fprintf fmt "(%a) %a" pp t1 pp t2
    | Pair (t1, t2) ->
      Format.fprintf fmt "(%a, %a)" pp t1 pp t2

end

open Terms

let x = mk "x"
let y = mk "y"
let a = mk "a"
let b = mk "b"


let t = Pair (Var x, Var y)
let t = Pair (t, t)

let p1 = PPair (PVar x, PVar y)
let p2 = PPair (PVar a, PVar b)
let p = PPair (p1, p2)
let pb = unbox
  (bind_p p (_Pair (_Var x) (_Var y)))

let p, _ = unbind_p pb

let test () =
  Format.printf "%a" pp_p p