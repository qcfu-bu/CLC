module Id : sig
  type t

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val of_string : string -> t

  val refresh : t -> t

  val pp : Format.formatter -> t -> unit
end

module Name : sig
  type t = Anonymous | Name of Id.t

  val mk_name : Id.t -> t

  val is_anonymous : t -> bool

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit
end

type t = Name.t = Anonymous | Name of Id.t
