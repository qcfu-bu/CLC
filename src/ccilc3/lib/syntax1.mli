open Names

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type 'a abs [@@deriving show { with_path = false }]
and 'a pabs

and tm =
  | Ann of tm * tm
  | Meta of V.t * tms
  | Type of sort
  | Var of V.t
  | Pi of sort * tm * tm abs
  | Fun of tm_opt * cls abs
  | App of tm * tm
  | Let of tm * tm abs
  | Data of D.t * tms
  | Cons of C.t * tms
  | Match of tms * cls
  | If of tm * tm * tm
  | Main
  | Proto
  | End
  | Act of bool * tm * tm abs
  | Ch of bool * tm
  | Fork of tm * tm * tm abs
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

type target =
  | TStdin
  | TStdout
  | TStderr
  | TMain
[@@deriving show { with_path = false }]

type decl =
  | DTm of V.t * tm_opt * tm
  | DFun of V.t * tm * cls abs
  | DData of D.t * ptl * conss
  | DOpen of target * V.t
[@@deriving show { with_path = false }]

and decls = decl list
and cons = Cons of C.t * ptl
and conss = cons list

and ptl =
  | PBase of tl
  | PBind of tm * ptl abs

and tl =
  | TBase of tm
  | TBind of tm * tl abs

val bind_tm : V.t -> tm -> tm abs
val bindp_tm : ps -> tm -> tm pabs
val bind_ptl : V.t -> ptl -> ptl abs
val bind_tl : V.t -> tl -> tl abs
val unbind_tm : tm abs -> V.t * tm
val unbindp_tm : tm pabs -> ps * tm
val unbind2_tm : tm abs -> tm abs -> V.t * tm * tm
val unbindp2_tm : tm pabs -> tm pabs -> ps * tm * tm