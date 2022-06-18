open Format
open Bindlib
open Name
open Core
open Prelude

let pp_v fmt x = fprintf fmt "%s" (name_of x)

module PrintTerm = struct
  open Tm

  let rec nat_of m =
    match m with
    | Constr (id, []) when Id.equal id Prelude.o_id -> Some 0
    | Constr (id, [ m ]) when Id.equal id Prelude.s_id -> (
      match nat_of m with
      | Some n -> Some (1 + n)
      | None -> None)
    | _ -> None

  let bin_of ms =
    List.map
      (fun m ->
        match m with
        | Constr (id, []) when Id.equal Prelude.true_id id -> Some 1
        | Constr (id, []) when Id.equal Prelude.false_id id -> Some 0
        | _ -> None)
      ms

  let dec_of ns =
    List.fold_left
      (fun acc opt ->
        match (acc, opt) with
        | Some acc, Some n -> Some ((acc * 2) + n)
        | _ -> None)
      (Some 0) ns

  let char_of m =
    match m with
    | Constr (id, ms) when Id.equal Prelude.ascii0_id id -> (
      let n = ms |> bin_of |> dec_of in
      match n with
      | Some n -> Some (Char.chr n)
      | None -> None)
    | _ -> None

  let rec string_of m =
    match m with
    | Constr (id, []) when Id.equal Prelude.emptyString_id id -> Some ""
    | Constr (id, [ m; n ]) when Id.equal Prelude.string0_id id -> (
      match (char_of m, string_of n) with
      | Some c, Some s -> Some (sprintf "%c%s" c s)
      | _ -> None)
    | _ -> None

  let rec pp_p fmt p =
    match p with
    | PVar x -> pp_v fmt x
    | PInd (id, []) -> fprintf fmt "%a" Id.pp id
    | PInd (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps
    | PConstr (id, []) -> fprintf fmt "%a" Id.pp id
    | PConstr (id, ps) -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ps ps

  and pp_ps fmt ps =
    match ps with
    | [ p ] -> pp_p fmt p
    | p :: ps -> fprintf fmt "@[%a@;<1 2>%a@]" pp_p p pp_ps ps
    | _ -> ()

  let rec pp fmt m =
    let rec spine s m =
      match m with
      | Lam (t, b) ->
        if s = t then
          let x, m = unbind b in
          let xs, m = spine s m in
          (x :: xs, m)
        else
          ([], m)
      | _ -> ([], m)
    in
    match m with
    | Ann (m, a) -> fprintf fmt "@[((%a) :@;<1 2>%a)@]" pp m pp a
    | Meta x -> Meta.pp fmt x
    | Knd s -> (
      match s with
      | U -> fprintf fmt "U"
      | L -> fprintf fmt "L")
    | Var x -> pp_v fmt x
    | Pi (s, a, b) -> (
      let x, ub = unbind b in
      match s with
      | U ->
        if binder_occur b then
          fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x pp a pp
            ub
        else
          fprintf fmt "@[(%a) ->@;<1 2>%a@]" pp a pp ub
      | L ->
        if binder_occur b then
          fprintf fmt "@[@[linear (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x pp a pp
            ub
        else
          fprintf fmt "@[(%a) -o@;<1 2>%a@]" pp a pp ub)
    | Lam (s, m) -> (
      let x, um = unbind m in
      let xs, um = spine s um in
      match s with
      | U -> fprintf fmt "@[fun %a%a =>@;<1 2>%a@]" pp_v x pp_vs xs pp um
      | L -> fprintf fmt "@[lin %a%a =>@;<1 2>%a@]" pp_v x pp_vs xs pp um)
    | App (m, n) -> fprintf fmt "@[(%a)@;<1 2>%a@]" pp m pp n
    | Let (m, n) ->
      let x, un = unbind n in
      fprintf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" pp_v x pp m pp
        un
    | Ind (id, ms) -> (
      match ms with
      | [] -> Id.pp fmt id
      | _ -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms)
    | Constr (id, ms) -> (
      match ms with
      | [] -> Id.pp fmt id
      | _ ->
        if Id.equal id Prelude.o_id || Id.equal id Prelude.s_id then
          match nat_of m with
          | Some n -> fprintf fmt "%d" n
          | None -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms
        else if
          Id.equal id Prelude.string0_id || Id.equal id Prelude.emptyString_id
        then
          match string_of m with
          | Some s -> fprintf fmt "\"%s\"" (String.escaped s)
          | None -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms
        else if Id.equal id Prelude.ascii0_id then
          match char_of m with
          | Some c -> fprintf fmt "\'%s\'" (Char.escaped c)
          | None -> fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms
        else
          fprintf fmt "@[(%a@;<1 2>%a)@]" Id.pp id pp_ts ms)
    | Match (m, mot, cls) ->
      fprintf fmt "@[<v 0>@[match %a%a@;<1 0>with@]@;<1 0>@[%a@]end@]" pp m pp_m
        mot pp_cls cls
    | Fix m ->
      let x, um = unbind m in
      let xs, um = spine U um in
      fprintf fmt "@[fix %a%a =>@;<1 2>%a@]" pp_v x pp_vs xs pp um
    | Main -> fprintf fmt "main"
    | Proto -> fprintf fmt "proto"
    | End -> fprintf fmt "$"
    | Act (r, a, b) ->
      let x, ub = unbind b in
      if r then
        fprintf fmt "@[?(%a : %a),@;<1 2>%a@]" pp_v x pp a pp ub
      else
        fprintf fmt "@[!(%a : %a),@;<1 2>%a@]" pp_v x pp a pp ub
    | Ch (r, m) ->
      if r then
        fprintf fmt "channel %a" pp m
      else
        fprintf fmt "channel- %a" pp m
    | Fork (a, m, n) ->
      let x, un = unbind n in
      fprintf fmt "@[@[fork (%a :@;<1 2>%a) :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
        pp_v x pp a pp m pp un
    | Send m -> fprintf fmt "send %a" pp m
    | Recv m -> fprintf fmt "recv %a" pp m
    | Close m -> fprintf fmt "close %a" pp m
    | Axiom (id, _) -> Id.pp fmt id

  and pp_vs fmt xs =
    match xs with
    | [] -> ()
    | [ x ] -> fprintf fmt " %a" pp_v x
    | x :: xs -> fprintf fmt " %a%a" pp_v x pp_vs xs

  and pp_ts fmt ms =
    match ms with
    | [ m ] -> pp fmt m
    | m :: ms -> fprintf fmt "@[%a@;<1 2>%a@]" pp m pp_ts ms
    | _ -> ()

  and pp_m fmt mot =
    match mot with
    | Mot0 -> ()
    | Mot1 mot ->
      let x, umot = unbind mot in
      fprintf fmt " as %a return@;<1 2>%a" pp_v x pp umot
    | Mot2 mot ->
      let p, umot = unbind_p mot in
      fprintf fmt " in %a return@;<1 2>%a" pp_p p pp umot
    | Mot3 mot ->
      let x, mot = unbind mot in
      let p, umot = unbind_p mot in
      fprintf fmt " as %a in %a return@;<1 2>%a" pp_v x pp_p p pp umot

  and pp_cl fmt cl =
    let p, ucl = unbind_p cl in
    fprintf fmt "@[| %a =>@;<1 2>%a@]" pp_p p pp ucl

  and pp_cls fmt cls =
    match cls with
    | [] -> ()
    | cl :: cls -> fprintf fmt "@[<v 0>%a@;<1 0>%a@]" pp_cl cl pp_cls cls
end

module PrintTop = struct
  open Tp

  let rec pp fmt t =
    match t with
    | Main m -> fprintf fmt "@[Definition Main :=@;<1 2>%a.@]" PrintTerm.pp m
    | Define (m, t) -> (
      match m with
      | Axiom (_, m) ->
        let x, ut = unbind t in
        fprintf fmt "@[Axiom %a :@;<1 2>%a.@.@.%a@]" pp_v x PrintTerm.pp m pp ut
      | _ ->
        let x, ut = unbind t in
        fprintf fmt "@[Definition %a :=@;<1 2>%a.@.@.%a@]" pp_v x PrintTerm.pp m
          pp ut)
    | Induct (Ind (id, a, cs), t) ->
      fprintf fmt "@[Inductive %a %a :=@.%a.@.@.%a@]" Id.pp id pp_pscope a
        pp_constr cs pp t
    | Import (id, m, t) ->
      let x, ut = unbind t in
      fprintf fmt "@[Import %a : %a.@.@.%a@]" pp_v x PrintTerm.pp m pp ut

  and pp_constr fmt cs =
    match cs with
    | [] -> ()
    | [ Constr (id, a) ] -> fprintf fmt "@[<v 0>| %a %a@]" Id.pp id pp_pscope a
    | Constr (id, a) :: cs ->
      fprintf fmt "@[<v 0>| %a %a@;<1 0>%a@]" Id.pp id pp_pscope a pp_constr cs

  and pp_pscope fmt a =
    match a with
    | PBase a -> fprintf fmt ": %a" pp_tscope a
    | PBind (a, b) ->
      let x, ub = unbind b in
      fprintf fmt "@[@[(%a :@;<1 2>%a)@]@;<1 2>%a@]" pp_v x PrintTerm.pp a
        pp_pscope ub

  and pp_tscope fmt a =
    match a with
    | TBase a -> Tm.pp fmt a
    | TBind (a, b) ->
      let x, ub = unbind b in
      if binder_occur b then
        fprintf fmt "@[@[forall (%a :@;<1 2>%a),@]@;<1 2>%a@]" pp_v x
          PrintTerm.pp a pp_tscope ub
      else
        fprintf fmt "@[(%a) ->@;<1 2>%a@]" PrintTerm.pp a pp_tscope ub
end