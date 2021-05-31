type term =
    Var of term Bindlib.var
  | Ann of term * term
  | Type
  | Prod   of Rig.rig * term * (term, term) Bindlib.binder
  | Lambda of (term, term) Bindlib.binder
  | Fix    of (term, term) Bindlib.binder
  | App    of term * term

type tvar = term Bindlib.var

val _Var : 'a Bindlib.var -> 'a Bindlib.box
val _Ann : term Bindlib.box -> term Bindlib.box -> term Bindlib.box
val _Type : term Bindlib.box
val _Prod :
  Rig.rig ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _Lambda : (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _Fix : (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _App : term Bindlib.box -> term Bindlib.box -> term Bindlib.box

val lift : term -> term Bindlib.box

val pp : Format.formatter -> term -> unit