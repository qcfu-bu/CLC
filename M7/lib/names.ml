
module Id : sig
  type t

  val mk : string -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end
=
struct
  type t = {
    name : string;
    id   : int;
  }

  let stamp = ref (-1)

  let mk s = 
    incr stamp; {
      name = s;
      id   = !stamp
    }

  let compare t1 t2 = Int.compare t1.id t2.id

  let equal t1 t2 = Int.equal t1.id t2.id

  let pp fmt t =
    Format.fprintf fmt "%s_%d" t.name t.id
end