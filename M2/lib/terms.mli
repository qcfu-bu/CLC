type term =
    Var of term Bindlib.var
  | Type
  | Prod   of Ring.ring * term * (term, term) Bindlib.binder
  | Lambda of Ring.ring * term * (term, term) Bindlib.binder
  | Fix    of Ring.ring * term * (term, term) Bindlib.binder
  | LetIn  of Ring.ring * term * term * (term, term) Bindlib.binder
  | App of term * term
  | Magic

type tvar = term Bindlib.var

val _Var : 'a Bindlib.var -> 'a Bindlib.box
val _Type : term Bindlib.box
val _Prod :
  Ring.ring ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _Lambda :
  Ring.ring ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _Fix :
  Ring.ring ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _LetIn :
  Ring.ring ->
  term Bindlib.box ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _App : term Bindlib.box -> term Bindlib.box -> term Bindlib.box
val _Magic : term Bindlib.box

val lift : term -> term Bindlib.box

val pp : Format.formatter -> term -> unit