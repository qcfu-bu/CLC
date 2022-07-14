type id = string [@@deriving show { with_path = false }]
and id_opt = id option

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type tm =
  | Ann of tm * tm
  | Type of sort
  | Id of id
  | Pi of sort * args * tm
  | Fun of id_opt * tm_opt * cls
  | App of tm * tms
  | Let of p * tm * tm
  | Match of tms * cls
  | If of tm * tm * tm
  | Main
  | Proto
  | End
  | Act of bool * args * tm
  | Ch of bool * tm
  | Fork of id * tm * tm * tm
  | Send of tm
  | Recv of tm
  | Close of tm
[@@deriving show { with_path = false }]

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of id
  | PCons of id * ps
  | PAbsurd

and ps = p list
and arg = id_opt * tm * bool
and args = arg list
and cl = Cl of (ps * tm_opt)
and cls = cl list

type def =
  | DTm of id * tm_opt * tm
  | DFun of id * tm * cls
  | DInd of ind
  | DOpen of id
[@@deriving show { with_path = false }]

and ind = Ind of id * ptl * constrs
and constr = Constr of id * ptl
and constrs = constr list
and ptl = PTl of args * tl
and tl = Tl of args * tm