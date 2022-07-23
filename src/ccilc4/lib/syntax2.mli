open Names

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type 'a abs [@@deriving show { with_path = false }]
and 'a pabs

and tm =
  | Ann of tm * tm
  | Meta of M.t * tms
  | Type of sort
  | Var of V.t
  | Pi of sort * tm * bool * tm abs
  | Fix of tm * tm abs
  | Lam of sort * tm abs
  | App of tm * tm
  | Let of tm * tm abs
  | Data of D.t * tms
  | Cons of C.t * tms
  | Case of tm * tm * cls
  | Absurd
  | Main
  | Proto
  | End
  | Act of bool * sort * tm * tm abs
  | Ch of bool * tm
  | Fork of tm * tm * tm abs
  | Send of tm
  | Recv of sort * tm
  | Close of tm

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of V.t
  | PCons of C.t * ps

and ps = p list
and cl = Cl of tm pabs
and cls = cl list

type trg =
  | TStdin
  | TStdout
  | TStderr
  | TMain
[@@deriving show { with_path = false }]

type dcl =
  | DTm of V.t * tm * tm
  | DData of D.t * ptl * dconss
  | DOpen of trg * V.t
  | DAxiom of V.t * tm
[@@deriving show { with_path = false }]

and dcls = dcl list
and dcons = DCons of C.t * ptl
and dconss = dcons list

and ptl =
  | PBase of tl
  | PBind of tm * ptl abs

and tl =
  | TBase of tm
  | TBind of tm * bool * tl abs

val var : V.t -> tm
val xs_of_p : p -> V.t list
val bind_tm : V.t -> tm -> tm abs
val bindp_tm : p -> tm -> tm pabs
val bind_ptl : V.t -> ptl -> ptl abs
val bind_tl : V.t -> tl -> tl abs
val unbind_tm : tm abs -> V.t * tm
val unbindp_tm : tm pabs -> p * tm
val unbind_ptl : ptl abs -> V.t * ptl
val unbind_tl : tl abs -> V.t * tl
val unbind2_tm : tm abs -> tm abs -> V.t * tm * tm
val unbindp2_tm : tm pabs -> tm pabs -> p * tm * tm
val asubst_tm : tm abs -> tm -> tm
val asubst_tl : tl abs -> tm -> tl
val asubst_ptl : ptl abs -> tm -> ptl
val asubstp_tm : tm pabs -> tm -> tm
val subst_tm : V.t -> tm -> tm -> tm
val mLam : sort -> V.t list -> tm -> tm
val mkApps : tm -> tms -> tm
val unApps : tm -> tm * tms
val equal_abs : ('a -> 'b -> bool) -> 'a abs -> 'b abs -> bool
val equal_pabs : ('a -> 'b -> bool) -> 'a pabs -> 'b pabs -> bool
val occurs_tm : V.t -> tm -> bool
val occurs_tl : V.t -> tl -> bool