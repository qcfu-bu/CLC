open Bindlib
open Terms

let __ = new_var (fun x -> Var x) "_"
let mk = new_var (fun x -> Var x)

let ( ! ) = _Var
let ( >: ) = _Ann
let ty = _Type I
let li = _Type L
let forall x ty1 ty2 =  _Prod ty1 (bind_var x ty2)
let ( --> ) ty1 ty2 = forall __ ty1 ty2
let ( ->> ) ty1 ty2 = _Lolli ty1 ty2
let fn x t = _Lambda (bind_var x t)
let ( $ ) t1 t2 = _App t1 t2
let let_ x t1 t2 =
  _LetIn t1 (bind_var x t2)
let ( === ) t1 t2 = _Eq t1 t2
let refl = _Refl
let ind = _Ind
let nat = _Nat
let z = _Zero
let s = _Succ
let indn = _Nat_elim
let gen = _G
let pack = _G_intro
let unpack = _G_elim
let embeding x ty1 ty2 = _F ty1 (bind_var x ty2)
let embed = _F_intro
let let_f (x, y) t1 t2 =
  _F_elim t1 (bind_mvar [| x; y |] t2)
let exists x ty1 ty2 =
  _Sum ty1 (bind_var x ty2)
let ( * ) ty1 ty2 = exists __ ty1 ty2
let ( ^ ) ty1 ty2 = _Tensor ty1 ty2
let ( & ) ty1 ty2 = _And ty1 ty2
let p (t1, t2) = _Pair t1 t2
let proj1 t = _Proj1 t
let proj2 t = _Proj2 t
let let_t (x, y) t1 t2 =
  _Tensor_elim t1 (bind_mvar [| x; y |] t2)
let unit_ty = _Unit I
let unit_li = _Unit L
let void = _True
let unit = _U
let let_u t1 t2 = _Unit_elim t1 t2
let axiom x ty t = _Axiom ty (bind_var x t)