open Bindlib
open Terms

let mk = mk
let __ = __

let ( ! ) = _Var
let ( >: ) = _Ann
let ty = _Type
let ln = _Linear
let tyProd x ty1 ty2 =  _TyProd ty1 (bind_var x ty2)
let lnProd x ty1 ty2 =  _LnProd ty1 (bind_var x ty2)
let ( --> ) ty1 ty2 = tyProd __ ty1 ty2
let ( ->> ) ty1 ty2 = lnProd __ ty1 ty2
let fn x t = _Lambda (bind_var x t)
let ( $ ) t1 t2 = _App t1 t2
let let_ x t1 t2 =
  _LetIn t1 (bind_var x t2)
let axiom x ty t = _Axiom ty (bind_var x t)