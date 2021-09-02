open Bindlib
open Names
open Terms

module Ctx : sig
  type entry =
    | Single of tvar * ty
    | Twin   of tvar * ty * ty
  type t
  val empty : t
  val add : t -> entry -> t
  val add1 : t -> tvar -> ty -> t
  val add2 : t -> tvar -> ty -> ty -> t
  val find : t -> tvar -> ty
  val pop : t -> (entry * t) option
  val findL : t -> tvar -> ty
  val findR : t -> tvar -> ty
  val fresh : t -> ty -> mvar * ty
  val app : Terms.t -> t -> Terms.t
end = struct
  type entry = 
    | Single of tvar * ty
    | Twin   of tvar * ty * ty

  type t = entry list

  let empty = []

  let add ctx p = p :: ctx
  let add1 ctx x ty = Single (x, ty) :: ctx
  let add2 ctx x ty1 ty2 = Twin (x, ty1, ty2) :: ctx

  let rec find ctx x =
    match ctx with
    | Single (y, ty) :: ctx ->
      if eq_vars x y 
      then ty
      else find ctx x
    | Twin _ :: ctx -> find ctx x
    | [] -> failwith (Format.asprintf "cannot find %a" pp_v x)

  let pop ctx =
    match ctx with
    | p :: ctx ->
      Some (p, ctx)
    | [] -> None

  let rec findL ctx x =
    match ctx with
    | Twin (y, ty, _) :: ctx ->
      if eq_vars x y 
      then ty
      else findL ctx x
    | Single _ :: ctx -> findL ctx x
    | [] -> failwith (Format.asprintf "cannot find %a" pp_v x)

  let rec findR ctx x =
    match ctx with
    | Twin (y, _, ty) :: ctx ->
      if eq_vars x y 
      then ty
      else findR ctx x
    | Single _ :: ctx -> findR ctx x
    | [] -> failwith (Format.asprintf "cannot find %a" pp_v x)

  let single = 
    List.map (fun p -> 
      match p with 
      | Single (x, ty) -> (x, ty)
      | Twin (x, ty, _) -> (x, ty))

  let fresh ctx ty =
    let ctx = single ctx in
    let ty = unbox (_Prod' ctx ty) in
    let ctx = List.map (fun (x, _) -> V x) ctx in
    let m = M.fresh ty in
    let m_app = unbox (_App' (M m) ctx) in
    (m, m_app)

  let app t ctx =
    let ctx = List.map (fun (x, _) -> V x) (single ctx) in
    unbox (_App' t ctx)
end

type entry = Ctx.entry
type eqn = Eqn of Ctx.t * t * ty * t * ty

let pp_eq fmt eqn =
  let Eqn (_, t1, ty1, t2, ty2) = eqn in
  Format.fprintf fmt "%a : %a === %a : %a" pp t1 pp ty1 pp t2 pp ty2