
module M : sig
  type 'a t
  val mk : string -> 'a t
  val fresh : unit -> 'a t
  val equal : 'a t -> 'a t -> bool
  val set : 'a t -> 'a -> unit
  val get : 'a t -> 'a option
  val pp : Format.formatter -> 'a t -> unit
end = 
struct
  type 'a t =  string * int * 'a option ref

  let stamp = ref 0

  let mk s =
    let id = !stamp in
    incr stamp;
    (s, id, ref None)

  let fresh () =
    let id = !stamp in
    incr stamp;
    ("", id, ref None)

  let equal m1 m2 =
    let (_, id1, _) = m1 in
    let (_, id2, _) = m2 in
    id1 = id2

  let set m a =
    let (_, _, r) = m in
    r := Some a

  let get m =
    let (_, _, r) = m in
    !r

  let pp fmt m =
    let (s, id, _) = m in
    Format.fprintf fmt "?%s_%d" s id
end

module P : sig
  type t
  val fresh : unit -> t
end =
struct
  type t = int

  let stamp = ref 0

  let fresh () = 
    let id = !stamp in
    incr stamp;
    id
end