open Names

type ('a, 'b) binder_rec = { binder : 'a; annot : 'b; q : int }

type ('a, 'b) binder = ('a, 'b) binder_rec

type ('constr, 'types) kind_of_term =
  | Rel of int
  | Var of Id.t
  | Type
  | Prod of (Name.t, 'types) binder * 'types
  | Lambda of (Name.t, 'types) binder * 'constr
  | Fix of (Name.t, 'types) binder * 'constr
  | App of 'constr * 'constr
  | Magic

type t = (t, t) kind_of_term

let rec_of_binder binder = binder

let bind br t =
  match br.binder with
  | Anonymous -> (br, t)
  | Name id1 ->
    let rec bind_i i t =
      match t with
      | Rel j -> Rel j
      | Var id2 -> if Id.equal id1 id2 then Rel i else Var id2
      | Type -> Type
      | Prod (b, t) ->
        let b = { b with annot = bind_i i b.annot } in
        let t = bind_i (i + 1) t in
        Prod (b, t)
      | Lambda (b, t) ->
        let b = { b with annot = bind_i i b.annot } in
        let t = bind_i (i + 1) t in
        Lambda (b, t)
      | Fix (b, t) ->
        let b = { b with annot = bind_i i b.annot } in
        let t = bind_i (i + 1) t in
        Fix (b, t)
      | App (t1, t2) ->
        let t1 = bind_i i t1 in
        let t2 = bind_i i t2 in
        App (t1, t2)
      | Magic -> Magic
    in
    (br, bind_i 0 t)

let rec unbind_i i id = function
  | Rel j -> if i = j then Var id else Rel j
  | Var id -> Var id
  | Type -> Type
  | Prod (b, t) ->
    let b = { b with annot = unbind_i i id b.annot } in
    let t = unbind_i (i + 1) id t in
    Prod (b, t)
  | Lambda (b, t) ->
    let b = { b with annot = unbind_i i id b.annot } in
    let t = unbind_i (i + 1) id t in
    Lambda (b, t)
  | Fix (b, t) ->
    let b = { b with annot = unbind_i i id b.annot } in
    let t = unbind_i (i + 1) id t in
    Fix (b, t)
  | App (t1, t2) ->
    let t1 = unbind_i i id t1 in
    let t2 = unbind_i i id t2 in
    App (t1, t2)
  | Magic -> Magic

let unbind b t =
  match b.binder with
  | Anonymous -> (b, t)
  | Name id ->
    let id = Id.refresh id in
    let b = { b with binder = Name id } in
    (b, unbind_i 0 id t)

let unbind2 b t1 t2 =
  match b.binder with
  | Anonymous -> (b, t1, t2)
  | Name id ->
    let id = Id.refresh id in
    let b = { b with binder = Name id } in
    let t1 = unbind_i 0 id t1 in
    let t2 = unbind_i 0 id t2 in
    (b, t1, t2)

let rec subst b t s =
  match t with
  | Rel _ -> t
  | Var id1 -> (
    match b.binder with
    | Name.Anonymous -> t
    | Name.Name id2 -> if Id.equal id1 id2 then s else t)
  | Type -> Type
  | Prod (bind, t) ->
    let bind = { bind with annot = subst b bind.annot s } in
    let t = subst b t s in
    Prod (bind, t)
  | Lambda (bind, t) ->
    let bind = { bind with annot = subst b bind.annot s } in
    let t = subst b t s in
    Lambda (bind, t)
  | Fix (bind, t) ->
    let bind = { bind with annot = subst b bind.annot s } in
    let t = subst b t s in
    Fix (bind, t)
  | App (t1, t2) ->
    let t1 = subst b t1 s in
    let t2 = subst b t2 s in
    App (t1, t2)
  | Magic -> Magic

let rec pp fmt = function
  | Rel i -> Format.fprintf fmt "Rel(%d)" i
  | Var id -> Format.fprintf fmt "Var(%a)" Id.pp id
  | Type -> Format.fprintf fmt "Type"
  | Prod (b, t) ->
    Format.fprintf fmt "Prod(%a, %a, p:%d, %a)" Name.pp b.binder pp b.annot b.q
      pp t
  | Lambda (b, t) ->
    Format.fprintf fmt "Lambda(%a, %a, p:%d, %a)" Name.pp b.binder pp b.annot
      b.q pp t
  | Fix (b, t) ->
    Format.fprintf fmt "Fix(%a, %a, p:%d, %a)" Name.pp b.binder pp b.annot b.q
      pp t
  | App (t1, t2) -> Format.fprintf fmt "App(%a, %a)" pp t1 pp t2
  | Magic -> Format.fprintf fmt "Magic"
