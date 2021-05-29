open Ast

let rec eq t1 t2 =
  if aeq t1 t2 then true
  else
    let t1 = whnf t1 in
    let t2 = whnf t2 in
    eq_term t1 t2

and eq_term t1 t2 =
  match (t1, t2) with
  | Var v1, Var v2 -> Var.eq v1 v2
  | TT, TT -> true
  | Fun t1, Fun t2 ->
      let arg_type = eq t1.arg_type t2.arg_type in
      let out_type = eq t1.out_type t2.out_type in
      let quantity = t1.quantity = t2.quantity in
      arg_type && out_type && quantity
  | Fix t1, Fix t2 ->
      let bod_term = eq t1.bod_term t2.bod_term in
      let arg_type = eq t1.arg_type t2.arg_type in
      let out_type = eq t1.out_type t2.out_type in
      let quantity = t1.quantity = t2.quantity in
      bod_term && arg_type && out_type && quantity
  | App t1, App t2 ->
      let fun_term = eq t1.fun_term t2.fun_term in
      let arg_term = eq t1.arg_term t2.arg_term in
      let arg_type = eq t1.arg_type t2.arg_type in
      let out_type = eq t1.out_type t2.out_type in
      let quantity = t1.quantity = t2.quantity in
      fun_term && arg_term && arg_type && out_type && quantity
  | Magic, _ -> true
  | _, Magic -> true
  | _ -> false

and whnf t =
  match t with
  | Var _ -> t
  | TT -> t
  | Fun _ -> t
  | Fix _ -> t
  | App t -> (
      let fun_term = whnf t.fun_term in
      let arg_term = whnf t.arg_term in
      match fun_term with
      | Fix t ->
          let bod_term = subst t.fun_name t.bod_term (Fix t) in
          let bod_term = subst t.arg_name bod_term arg_term in
          whnf bod_term
      | _ ->
          App
            {
              fun_term;
              arg_term;
              arg_name = t.arg_name;
              arg_type = t.arg_type;
              out_type = t.out_type;
              quantity = t.quantity;
            })
  | Magic -> t

module Debug = struct
  let wc = Var.mk "_"

  let f = Var.mk "f"

  let x = Var.mk "x"

  let app t1 t2 =
    App
      {
        fun_term = t1;
        arg_term = t2;
        arg_name = wc;
        arg_type = Magic;
        out_type = Magic;
        quantity = 0;
      }

  let f1 =
    Fix
      {
        fun_name = f;
        arg_name = x;
        bod_term = Var x;
        arg_type = Magic;
        out_type = Magic;
        quantity = 0;
      }

  let f2 = app f1 f1

  let r1 = eq f1 f2

  let r2 = subst x f1 f2
end
