type id = string [@@deriving show]

type sort =
  | U
  | L
[@@deriving show]

type tm =
  | Ann of tm * tm
  | Meta
  | Knd of sort
  | Id of id
  | Pi of sort * args * tm
  | Fun of sort * id * tm_opt * cls
  | App of tm * tms
  | Let of p * tm * tm
  | Match of tms * tm_opt * cls
  | Main
  | Proto
  | End
  | Act of bool * id * tm * tm
  | Ch of bool * tm
  | Fork of id * tm * tm * tm
  | Send of tm
  | Recv of tm
  | Close of tm
[@@deriving show]

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of id
  | PCons of id * ps

and ps = p list
and arg = id * tm * bool
and args = arg list
and cl = Cl of (p * tm)
and cls = cl list

type def =
  | DTm of id * tm_opt * tm
  | DFun of id * tm * cls
  | DInd of ind
  | DOpen of id
[@@deriving show]

and ind = Ind of id * ptl * constrs
and constr = Constr of id * ptl
and constrs = constr list
and ptl = PTl of args * tl
and tl = Tl of args * tm