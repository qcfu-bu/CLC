module Name : sig
  type t

  val string_of : t -> string

  val mk : string -> t

  val __ : t

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val pp : Format.formatter -> t -> unit
end = struct
  type t = string * int

  let stamp = ref (-1)

  let string_of t = fst t

  let mk s =
    incr stamp;
    (s, !stamp)

  let __ = mk "_"

  let equal t1 t2 = Int.equal (snd t1) (snd t2)

  let compare t1 t2 = Int.compare (snd t1) (snd t2)

  let pp fmt t = Format.fprintf fmt "%s_%d" (fst t) (snd t)
end

module Meta : sig
  type t

  val mk : unit -> t

  val id : t -> int

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val pp : Format.formatter -> t -> unit
end = struct
  type t = int

  let stamp = ref (-1)

  let mk () =
    incr stamp;
    !stamp

  let id t = t

  let equal m1 m2 =
    let id1 = m1 in
    let id2 = m2 in
    id1 = id2

  let compare m1 m2 =
    let id1 = m1 in
    let id2 = m2 in
    Int.compare id1 id2

  let pp fmt m = Format.fprintf fmt "?%d" m
end

module Id : sig
  type t

  val get_name : t -> string

  val get_id : t -> int

  val get_ind : t -> bool

  val get_arity : t -> int

  val set_arity : t -> int -> t

  val mk : string -> ?ind:bool -> ?arity:int -> unit -> t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit
end = struct
  type t_rec =
    { name : string
    ; id : int
    ; ind : bool
    ; arity : int
    }

  type t = t_rec ref

  let get_name t = !t.name

  let get_id t = !t.id

  let get_ind t = !t.ind

  let get_arity t = !t.arity

  let set_arity t n =
    let t_rec = !t in
    t := { t_rec with arity = n };
    t

  let stamp = ref (-1)

  let mk s ?ind:(t = false) ?arity:(n = 0) () =
    incr stamp;
    ref { name = s; id = !stamp; ind = t; arity = n }

  let compare t1 t2 = Int.compare !t1.id !t2.id

  let equal t1 t2 = Int.equal !t1.id !t2.id

  let pp fmt t =
    if !t.ind then
      Format.fprintf fmt "%s_%d" !t.name !t.id
    else
      Format.fprintf fmt "%s_%d" !t.name !t.id
end
