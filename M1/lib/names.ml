module Id = struct
  type t = string

  let equal = String.equal
  let compare = String.compare
  let of_string s = s
  let pp fmt id = Format.fprintf fmt "%s" id
end

module Name = struct
  type t =
    | Anonymous
    | Name of Id.t

  let mk_name id = Name id

  let is_anonymous = function
    | Anonymous -> true
    | Name _ -> false
  ;;

  let compare n1 n2 =
    match n1, n2 with
    | Anonymous, Anonymous -> 0
    | Name id1, Name id2 -> Id.compare id1 id2
    | Anonymous, Name _ -> -1
    | Name _, Anonymous -> 1
  ;;

  let equal n1 n2 =
    match n1, n2 with
    | Anonymous, Anonymous -> true
    | Name id1, Name id2 -> Id.equal id1 id2
    | _ -> false
  ;;

  let pp fmt = function
    | Anonymous -> Format.fprintf fmt "_"
    | Name id -> Format.fprintf fmt "%a" Id.pp id
  ;;
end
