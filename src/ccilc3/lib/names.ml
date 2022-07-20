open Fmt

module V : sig
  type t

  val mk : string -> t
  val bind : int -> t
  val blank : unit -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val freshen : t -> t
  val is_bound : t -> int -> int -> int option
  val pp : Format.formatter -> t -> unit
end = struct
  type t =
    | Free of string * Int64.t
    | Bound of int

  let stamp = ref Int64.zero

  let mk s =
    let _ = stamp := Int64.succ !stamp in
    Free (s, !stamp)

  let bind k = Bound k
  let blank () = mk ""

  let equal x y =
    match (x, y) with
    | Free (_, x), Free (_, y) -> Int64.equal x y
    | Bound x, Bound y -> x = y
    | _ -> false

  let compare x y = compare x y

  let freshen x =
    match x with
    | Bound _ -> x
    | Free (x, _) ->
      let _ = stamp := Int64.succ !stamp in
      Free (x, !stamp)

  let is_bound x sz k =
    match x with
    | Bound i ->
      if k <= i && i < k + sz then
        Some i
      else
        None
    | Free _ -> None

  let pp fmt x =
    match x with
    | Bound x -> pf fmt "_%d" x
    | Free (x, id) -> pf fmt "%s_%s" x (Int64.to_string id)
end

module M : sig
  type t

  val mk : unit -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = int

  let stamp = ref 0

  let mk () =
    incr stamp;
    !stamp

  let equal x y = x = y
  let compare x y = Int.compare x y
  let pp fmt id = pf fmt "??%d" id
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
  let compare x y = Int.compare (snd x) (snd y)
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
  let compare x y = Int.compare (snd x) (snd y)
  let pp fmt (s, id) = pf fmt "%s_c%d" s id
end

module SSet = Set.Make (String)
module VSet = Set.Make (V)
module MSet = Set.Make (M)
module CSet = Set.Make (C)
module DSet = Set.Make (D)
module SMap = Map.Make (String)
module VMap = Map.Make (V)
module MMap = Map.Make (M)
module CMap = Map.Make (C)
module DMap = Map.Make (D)