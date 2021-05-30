type term =
    Var of term Bindlib.var
  | Type
  | Prod of int * term * (term, term) Bindlib.binder
  | Lambda of int * term * (term, term) Bindlib.binder
  | Fix of int * term * (term, term) Bindlib.binder
  | App of term * term
  | Magic

type tvar = term Bindlib.var

val lift : term -> term Bindlib.box