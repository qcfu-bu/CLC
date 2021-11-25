open Names

type 'a elem_q = { elem : 'a; q : int }

type 'a t

val empty : 'a t

val add : Id.t -> 'a elem_q -> 'a t -> 'a t

val remove : Id.t -> 'a t -> 'a t

val find : Id.t -> 'a t -> 'a elem_q

val equal : 'a t -> 'a t -> bool

val scale : int -> 'a t -> 'a t

val sum : 'a t -> 'a t -> 'a t

val sub : 'a t -> 'a t -> 'a t

val is_positive : 'a t -> bool

val is_zero : 'a t -> bool
