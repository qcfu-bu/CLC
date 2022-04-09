open Format
open Bindlib

module Meta : sig
  type t

  val mk : unit -> t

  val equal : t -> t -> bool

  val pp : formatter -> t -> unit
end = struct
  type t = int

  let stamp = ref 0

  let mk () =
    let i = !stamp in
    let _ = incr stamp in
    i

  let equal i1 i2 = i1 = i2

  let pp fmt i = fprintf fmt "?%d" i
end

module Id : sig
  type t

  val mk : string -> t

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val pp : formatter -> t -> unit

  val pp_debug : formatter -> t -> unit

  val tt_id : t

  val pair_id : t
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    let i = !stamp in
    let _ = incr stamp in
    (s, i)

  let equal (_, i1) (_, i2) = i1 = i2

  let compare (_, i1) (_, i2) = Int.compare i1 i2

  let pp fmt (s, _) = fprintf fmt "%s" s

  let pp_debug fmt (s, i) = fprintf fmt "%s#%d" s i

  let tt_id = mk "unit"

  let pair_id = mk "pair"
end