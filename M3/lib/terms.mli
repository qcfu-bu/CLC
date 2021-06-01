type term =
    Var of term Bindlib.var
  | AnnTy of term * term
  | AnnVr of term * term Bindlib.var
  | Type
  | Prod   of Rig.rig * term * (term, term) Bindlib.binder
  | Lambda of (term, term) Bindlib.binder
  | Fix    of (term, term) Bindlib.binder
  | App    of term * term
  | LetIn  of Rig.rig * term * (term, term) Bindlib.binder

type tvar = term Bindlib.var

val __ : tvar
val mk : string -> tvar

val _Var : 'a Bindlib.var -> 'a Bindlib.box
val _AnnTy : term Bindlib.box -> term Bindlib.box -> term Bindlib.box
val _AnnVr : 
  term Bindlib.box -> term Bindlib.var -> term Bindlib.box
val _Type : term Bindlib.box
val _Prod :
  Rig.rig ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _Lambda : (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _Fix : (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box
val _App : term Bindlib.box -> term Bindlib.box -> term Bindlib.box
val _LetIn :
  Rig.rig ->
  term Bindlib.box ->
  (term, term) Bindlib.binder Bindlib.box -> term Bindlib.box

val lift : term -> term Bindlib.box

val pp : Format.formatter -> term -> unit