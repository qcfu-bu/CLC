module Name : sig
  type t

  val string_of : t -> string
  val mk : string -> t
  val __ : t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end =
struct
  type t = string * int
  let stamp = ref (-1)

  let string_of t = fst t
  let mk s = incr stamp; (s, !stamp)
  let __ = mk "_"
  let equal t1 t2 = Int.equal (snd t1) (snd t2)
  let compare t1 t2 = Int.compare (snd t1) (snd t2)
  let pp fmt t = Format.fprintf fmt "%s_%d" (fst t) (snd t)
end

module Meta : sig
  type 'a t

  val equal : 'a t -> 'a t -> bool
  val get : 'a t -> 'a option
  val set : 'a t -> 'a -> unit
  val pp_a : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end =
struct
  type 'a t = int * 'a option ref

  let equal m1 m2 =
    let id1, _ = m1 in
    let id2, _ = m2 in
    id1 = id2

  let get m =
    let _, opt = m in
    match !opt with
    | Some t -> Some t
    | None -> None

  let set m t =
    let _, opt = m in
    match !opt with
    | Some _ -> failwith "cannot reset meta-variable"
    | None -> opt := Some t

  let pp_a pp fmt m =
    let id, opt = m in
    match !opt with
    | Some t -> Format.fprintf fmt "%a" pp t
    | None -> Format.fprintf fmt "?%d" id
end

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
    then Format.fprintf fmt "%s_%d" !t.name !t.id
    else Format.fprintf fmt "%s_%d" !t.name !t.id
end
