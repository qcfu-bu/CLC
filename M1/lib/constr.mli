open Names

type ('a, 'b) binder_rec = { binder : 'a; annot : 'b; q : int }

type ('a, 'b) binder

type ('constr, 'types) kind_of_term =
  | Rel of int
  | Var of Id.t
  | Type
  | Prod of (Name.t, 'types) binder * 'types
  | Lambda of (Name.t, 'types) binder * 'constr
  | Fix of (Name.t, 'types) binder * 'constr
  | App of 'constr * 'constr
  | Magic

type t = (t, t) kind_of_term

val rec_of_binder : ('a, 'b) binder -> ('a, 'b) binder_rec

val bind : (Name.t, t) binder_rec -> t -> (Name.t, t) binder * t

val unbind : (Name.t, t) binder -> t -> (Name.t, t) binder * t

val unbind2 : (Name.t, t) binder -> t -> t -> (Name.t, t) binder * t * t

val subst : (Name.t, t) binder -> t -> t -> t
