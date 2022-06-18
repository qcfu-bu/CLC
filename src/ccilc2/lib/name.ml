open Format
open Bindlib

module Meta : sig
  type t

  val mk : unit -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : formatter -> t -> unit
end = struct
  type t = int

  let stamp = ref 0

  let mk () =
    let i = !stamp in
    let _ = incr stamp in
    i

  let equal i1 i2 = i1 = i2
  let compare i1 i2 = Int.compare i1 i2
  let pp fmt i = fprintf fmt "?%d" i
end

module Var : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : formatter -> t -> unit
  val pp_debug : formatter -> t -> unit
  val var : ('a var -> 'a) -> t -> 'a var
  val string_of : t -> string
  val __ : t
  val main : t
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
  let var f (s, _) = new_var f s
  let string_of (s, _) = s
  let __ = mk "_"
  let main = mk "_main_"
end

module Id : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : formatter -> t -> unit
  val pp_debug : formatter -> t -> unit
  val string_of : t -> string
  val stdin_id : t
  val stdout_id : t
  val stderr_id : t
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
  let string_of (s, _) = s
  let stdin_id = mk "stdin_t"
  let stdout_id = mk "stdout_t"
  let stderr_id = mk "stderr_t"
end

module IMap = Map.Make (Id)
module MMap = Map.Make (Meta)
module VMap = Map.Make (Var)