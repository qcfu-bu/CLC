open Names

type value =
  | Zero
  | Reg of V.t
  | Env of int
  | Proj of value * int

and values = value list

and proc =
  { name : V.t
  ; arg : V.t
  ; body : instrs
  ; return : value
  }

and chs = V.t list
and def = proc list

and instr =
  | Mov of V.t * value
  | Clo of V.t * V.t * values
  | Call of V.t * value * value
  | Struct of V.t * int * values
  | Switch of value * cls
  | Break
  | Open of V.t
  | Fork of V.t * value * V.t * values
  | Send of V.t * value
  | Recv of V.t * value
  | Close of V.t

and instrs = instr list
and cl = int * instrs
and cls = cl list