module Var : sig
  type t

  val eq : t -> t -> bool

  val compare : t -> t -> int

  val mk : string -> t

  val pp : Format.formatter -> t -> unit
end = struct
  type t = { name : string; idx : int }

  let stamp = ref 0

  let eq v1 v2 = v1.idx = v2.idx

  let compare v1 v2 = Int.compare v1.idx v2.idx

  let mk s =
    let v = { name = s; idx = !stamp } in
    stamp := !stamp + 1;
    v

  let pp fmt v = Format.fprintf fmt "%s#%d" v.name v.idx
end

type ty = term

and term =
  | Var of Var.t
  | TT
  | Fun of { arg_name : Var.t; arg_type : ty; out_type : ty; quantity : int }
  | Fix of {
      fun_name : Var.t;
      arg_name : Var.t;
      bod_term : term;
      arg_type : ty;
      out_type : ty;
      quantity : int;
    }
  | App of {
      fun_term : term;
      arg_term : term;
      arg_name : Var.t;
      arg_type : ty;
      out_type : ty;
      quantity : int;
    }
  | Magic

let pp (fmt : Format.formatter) t =
  match t with
  | Var v -> Var.pp fmt v
  | TT -> Format.fprintf fmt "TT"
  | Fun _ -> Format.fprintf fmt "Fun"
  | Fix _ -> Format.fprintf fmt "Fix"
  | App _ -> Format.fprintf fmt "App"
  | Magic -> Format.fprintf fmt "Magic"

let find_var ls v =
  let rec find_i i ls v =
    match ls with
    | [] -> None
    | v' :: ls -> if Var.eq v v' then Some i else find_i (i + 1) ls v
  in
  find_i 0 ls v

let aeq t1 t2 =
  let rec aeq_aux l1 l2 t1 t2 =
    match (t1, t2) with
    | Var v1, Var v2 -> (
        match (find_var l1 v1, find_var l2 v2) with
        | Some r1, Some r2 -> r1 = r2
        | None, None -> Var.eq v1 v2
        | _ -> false)
    | TT, TT -> true
    | Fun t1, Fun t2 ->
        let arg_type = aeq_aux l1 l2 t1.arg_type t2.arg_type in
        let out_type =
          aeq_aux (t1.arg_name :: l1) (t2.arg_name :: l2) t1.out_type
            t2.out_type
        in
        let quantity = t1.quantity = t2.quantity in
        arg_type && out_type && quantity
    | Fix t1, Fix t2 ->
        let fun_term =
          aeq_aux
            (t1.fun_name :: t1.arg_name :: l1)
            (t2.fun_name :: t2.arg_name :: l2)
            t1.bod_term t2.bod_term
        in
        let arg_type = aeq_aux l1 l2 t1.arg_type t2.arg_type in
        let out_type =
          aeq_aux (t1.arg_name :: l1) (t2.arg_name :: l2) t1.out_type
            t2.out_type
        in
        let quantity = t1.quantity = t2.quantity in
        fun_term && arg_type && out_type && quantity
    | App t1, App t2 ->
        let fun_term = aeq_aux l1 l2 t1.fun_term t2.fun_term in
        let arg_term = aeq_aux l1 l2 t1.arg_term t2.arg_term in
        let arg_type = aeq_aux l1 l2 t1.arg_type t2.arg_type in
        let out_type =
          aeq_aux (t1.arg_name :: l1) (t2.arg_name :: l2) t1.out_type
            t2.out_type
        in
        let quantity = t1.quantity = t2.quantity in
        fun_term && arg_term && arg_type && out_type && quantity
    | _ -> false
  in
  aeq_aux [] [] t1 t2

let rec subst v t s =
  match t with
  | Var v' -> if Var.eq v v' then s else t
  | TT -> t
  | Fun t ->
      let arg_type = subst v t.arg_type s in
      let out_type = subst v t.out_type s in
      Fun { arg_name = t.arg_name; arg_type; out_type; quantity = t.quantity }
  | Fix t ->
      let bod_term = subst v t.bod_term s in
      let arg_type = subst v t.arg_type s in
      let out_type = subst v t.out_type s in
      Fix
        {
          fun_name = t.fun_name;
          bod_term;
          arg_name = t.arg_name;
          arg_type;
          out_type;
          quantity = t.quantity;
        }
  | App t ->
      let fun_term = subst v t.fun_term s in
      let arg_term = subst v t.arg_term s in
      let arg_type = subst v t.arg_type s in
      let out_type = subst v t.out_type s in
      App
        {
          fun_term;
          arg_term;
          arg_name = t.arg_name;
          arg_type;
          out_type;
          quantity = t.quantity;
        }
  | Magic -> t
