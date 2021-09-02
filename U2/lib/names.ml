module M : sig
  type 'a t
  val fresh : 'a -> 'a t
  val equal : 'a t -> 'a t -> bool
  val set : 'a t -> 'a -> unit
  val get : 'a t -> 'a option
  val ty : 'a t -> 'a
  val pp : Format.formatter -> 'a t -> unit
end = 
struct
  type 'a t =  int * 'a option ref * 'a

  let stamp = ref 0

  let fresh ty =
    let id = !stamp in
    incr stamp;
    (id, ref None, ty)

  let equal m1 m2 =
    let (id1, _, _) = m1 in
    let (id2, _, _) = m2 in
    id1 = id2

  let set m a =
    let (_, r, _) = m in
    r := Some a

  let get m =
    let (_, r, _) = m in
    !r

  let ty m =
    let (_, _, ty) = m in
    ty

  let pp fmt m =
    let (id, _, _) = m in
    Format.fprintf fmt "?%d" id
end
