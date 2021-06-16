module Id : sig
  type t

  val get_name : t -> string
  val get_id : t -> int
  val get_tcons : t -> bool
  val get_arity : t -> int
  val set_arity : t -> int -> t

  val mk : string -> ?tcons:bool -> ?arity:int -> unit -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end
=
struct
  type t_rec = {
    name  : string;
    id    : int;
    tcons : bool;
    arity : int;
  } 

  type t = t_rec ref

  let get_name t = !t.name
  let get_id t = !t.id
  let get_tcons t = !t.tcons
  let get_arity t = !t.arity
  let set_arity t n =
    let t_rec = !t in
    t := { t_rec with arity = n }; t

  let stamp = ref (-1)

  let mk s ?tcons:(t=false) ?arity:(n=0) () = 
    incr stamp; ref {
      name  = s;
      id    = !stamp;
      tcons = t;
      arity = n;
    }

  let compare t1 t2 = Int.compare !t1.id !t2.id

  let equal t1 t2 = Int.equal !t1.id !t2.id

  let pp fmt t =
    if !t.tcons 
    then Format.fprintf fmt "T(%s#%d)" !t.name !t.id
    else Format.fprintf fmt "D(%s#%d)" !t.name !t.id
end