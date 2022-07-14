open Names

type sort =
  | U
  | L

type 'a abs = Abs of V.t * 'a
and 'a pabs = PAbs of ps * 'a

and tm =
  | Ann of tm * tm
  | Meta of V.t * tms
  | Type of sort
  | Var of V.t
  | Pi of sort * tm * tm abs
  | Fun of tm_opt * cls abs
  | App of tm * tm
  | Let of tm * tm abs
  | D of D.t * tms
  | C of C.t * tms
  | Match of tms * cls
  | If of tm * tm * tm
  | Main
  | Proto
  | End
  | Act of bool * tm * tm abs
  | Ch of bool * tm
  | Fork of tm * tm abs * tm
  | Send of tm
  | Recv of tm
  | Close of tm

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of V.t
  | PCons of C.t * ps
  | PAbsurd

and ps = p list
and cl = Cl of tm_opt pabs
and cls = cl list

let freshen_ps ps =
  let rec aux p =
    match p with
    | PVar x -> PVar (V.freshen x)
    | PCons (c, ps) -> PCons (c, List.map aux ps)
    | PAbsurd -> PAbsurd
  in
  List.map aux ps

let xs_of_ps ps =
  let rec aux p =
    match p with
    | PVar x -> [ x ]
    | PCons (_, ps) -> List.concat_map aux ps
    | PAbsurd -> []
  in
  List.map aux ps

let findi_opt f ls =
  let rec aux k ls =
    match ls with
    | [] -> None
    | h :: t ->
      if f k h then
        Some (k, h)
      else
        aux (k + 1) t
  in
  aux 0 ls

(* let bindn k xs m =
   let rec aux k m = *)
