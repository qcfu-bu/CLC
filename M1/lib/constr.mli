open Names

type ('a, 'b) binder_annot

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

val binder_of : ('a, 'b) binder_annot -> 'a

val annot_of : ('a, 'b) binder_annot -> 'b

val q_of : ('a, 'b) binder_annot -> int

val bind :
  binder:Name.t -> annot:t -> q:int -> t -> (Name.t, t) binder_annot * t

val unbind : binder:(Name.t, t) binder_annot -> t -> t

val subst : binder:(Name.t, t) binder_annot -> s:t -> t -> t
