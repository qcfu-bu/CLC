module Id = struct
  type t = { name : string; id : int }

  let stamp = ref 0

  let equal id1 id2 = id1.id = id2.id

  let compare id1 id2 = Int.compare id1.id id2.id

  let of_string s =
    let id = { name = s; id = !stamp } in
    let _ = incr stamp in
    id

  let refresh id =
    let id = { id with id = !stamp } in
    let _ = incr stamp in
    id

  let pp fmt id = Format.fprintf fmt "%s#%d" id.name id.id
end

module Name = struct
  type t = Anonymous | Name of Id.t

  let mk_name id = Name id

  let is_anonymous = function Anonymous -> true | Name _ -> false

  let compare n1 n2 =
    match (n1, n2) with
    | Anonymous, Anonymous -> 0
    | Name id1, Name id2 -> Id.compare id1 id2
    | Anonymous, Name _ -> -1
    | Name _, Anonymous -> 1

  let equal n1 n2 =
    match (n1, n2) with
    | Anonymous, Anonymous -> true
    | Name id1, Name id2 -> Id.equal id1 id2
    | _ -> false

  let pp fmt = function
    | Anonymous -> Format.fprintf fmt "_"
    | Name id -> Format.fprintf fmt "%a" Id.pp id
end

type t = Name.t = Anonymous | Name of Id.t
