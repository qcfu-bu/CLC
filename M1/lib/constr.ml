open Names

type ('a, 'b) binder_annot =
  { binder : 'a
  ; annot : 'b
  ; q : int
  }

type ('constr, 'types) kind_of_term =
  | Rel of int
  | Var of Id.t
  | Type
  | Prod of (Name.t, 'types) binder_annot * 'types
  | Lambda of (Name.t, 'types) binder_annot * 'constr
  | Fix of (Name.t, 'types) binder_annot * 'constr
  | App of 'constr * 'constr
  | Magic

type t = (t, t) kind_of_term

let binder_of binder = binder.binder
let annot_of binder = binder.annot
let q_of binder = binder.q

let bind ~binder ~annot ~q t =
  let rec bind_i i = function
    | Rel j -> Rel j
    | Var id1 ->
      (match binder with
      | Name.Anonymous -> Var id1
      | Name.Name id2 -> if Id.equal id1 id2 then Rel i else Var id1)
    | Type -> Type
    | Prod (b, t) ->
      let b = { b with annot = bind_i i b.annot } in
      let t = bind_i (i + 1) t in
      Prod (b, t)
    | Lambda (b, t) ->
      let b = { b with annot = bind_i i b.annot } in
      let t = bind_i (i + 1) t in
      Lambda (b, t)
    | Fix (b, t) ->
      let b = { b with annot = bind_i i b.annot } in
      let t = bind_i (i + 1) t in
      Fix (b, t)
    | App (t1, t2) ->
      let t1 = bind_i i t1 in
      let t2 = bind_i i t2 in
      App (t1, t2)
    | Magic -> Magic
  in
  let b = { binder; annot; q } in
  b, bind_i 0 t
;;

let unbind ~binder t =
  let rec unbind_i i = function
    | Rel j ->
      (match binder.binder with
      | Name.Anonymous -> Rel j
      | Name.Name id -> if i = j then Var id else Rel j)
    | Var id -> Var id
    | Type -> Type
    | Prod (b, t) ->
      let b = { b with annot = unbind_i i b.annot } in
      let t = unbind_i (i + 1) t in
      Prod (b, t)
    | Lambda (b, t) ->
      let b = { b with annot = unbind_i i b.annot } in
      let t = unbind_i (i + 1) t in
      Lambda (b, t)
    | Fix (b, t) ->
      let b = { b with annot = unbind_i i b.annot } in
      let t = unbind_i (i + 1) t in
      Fix (b, t)
    | App (t1, t2) ->
      let t1 = unbind_i i t1 in
      let t2 = unbind_i i t2 in
      App (t1, t2)
    | Magic -> Magic
  in
  unbind_i 0 t
;;

let rec subst ~binder ~s t =
  match t with
  | Rel _ -> t
  | Var id1 ->
    (match binder.binder with
    | Name.Anonymous -> t
    | Name.Name id2 -> if Id.equal id1 id2 then s else t)
  | Type -> Type
  | Prod (b, t) ->
    let b = { b with annot = subst ~binder ~s b.annot } in
    let t = subst ~binder ~s t in
    Prod (b, t)
  | Lambda (b, t) ->
    let b = { b with annot = subst ~binder ~s b.annot } in
    let t = subst ~binder ~s t in
    Lambda (b, t)
  | Fix (b, t) ->
    let b = { b with annot = subst ~binder ~s b.annot } in
    let t = subst ~binder ~s t in
    Fix (b, t)
  | App (t1, t2) ->
    let t1 = subst ~binder ~s t1 in
    let t2 = subst ~binder ~s t2 in
    App (t1, t2)
  | Magic -> Magic
;;
