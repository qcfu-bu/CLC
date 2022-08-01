open Names

type value =
  | Null
  | Var of V.t
  | Env of int
  | Proj of value * int
  | Ptr of V.t

and values = value list

type proc =
  { name : V.t
  ; arg : V.t
  ; body : instrs
  ; return : value
  }

and procs = proc list

and instr =
  | Mov of V.t * value
  | Clo of V.t * value * values
  | Call of V.t * value * value
  | Struct of V.t * C.t * values
  | Switch of value * cls

and instrs = instr list
and cl = Cl of C.t * instrs
and cls = cl list