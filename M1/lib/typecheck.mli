val check :
  Constr.t Context.t -> Constr.t -> int -> Constr.t -> Constr.t Context.t

val infer :
  Constr.t Context.t -> int -> Constr.t -> Constr.t Context.t * Constr.t
