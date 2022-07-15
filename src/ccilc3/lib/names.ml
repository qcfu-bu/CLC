open Fmt

module V : sig
  type t

  val blank : t
  val mk : string -> t
  val bind : int -> t
  val is_blank : t -> bool
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val freshen : t -> t
  val is_bound : t -> int -> int -> int option
  val pp : Format.formatter -> t -> unit
end = struct
  type t =
    | Free of string * int
    | Bound of int
    | Blank

  let stamp = ref 0
  let blank = Blank

  let mk s =
    incr stamp;
    Free (s, !stamp)

  let bind k = Bound k

  let is_blank x =
    match x with
    | Blank -> true
    | _ -> false

  let equal x y =
    match (x, y) with
    | Free (_, x), Free (_, y) -> x = y
    | Bound x, Bound y -> x = y
    | _ -> false

  let compare x y = compare x y

  let freshen x =
    match x with
    | Bound _ -> x
    | Free (x, _) ->
      incr stamp;
      Free (x, !stamp)
    | Blank -> Blank

  let is_bound x sz k =
    match x with
    | Bound i ->
      if k <= i && i < k + sz then
        Some i
      else
        None
    | Free _ -> None
    | Blank -> None

  let pp fmt x =
    match x with
    | Bound x -> pf fmt "_%d" x
    | Free (x, id) -> pf fmt "%s_%d" x id
    | Blank -> pf fmt "_"
end

module D : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = compare (snd x) (snd y)
  let pp fmt (s, id) = pf fmt "%s_d%d" s id
end

module C : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = compare (snd x) (snd y)
  let pp fmt (s, id) = pf fmt "%s_c%d" s id
end

module SSet = Set.Make (String)
module VSet = Set.Make (V)
module CSet = Set.Make (C)
module DSet = Set.Make (D)
module SMap = Map.Make (String)
module VMap = Map.Make (V)
module CMap = Map.Make (C)
module DMap = Map.Make (D)