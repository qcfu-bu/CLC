open Bindlib
open Names
open Terms

let x = mk "x"
let _A = mk "A"
let _B = mk "B"


(* Unit *)
let _Unit_id = Id.mk "Unit"
let _tt_id = Id.mk "tt"
let _tt = DConstr {
  name   = _tt_id;
  tscope = Base (TCons (_Unit_id, []))
}
let _Unit = TConstr {
  name   = _Unit_id;
  tscope = Base Type;
  constr = [_tt]
}

(* Bool *)
let _Bool_id = Id.mk "Bool"
let _true_id = Id.mk "true"
let _false_id = Id.mk "false"
let _true = DConstr {
  name = _true_id;
  tscope = Base (TCons (_Bool_id, []))
}
let _false = DConstr {
  name   = _false_id;
  tscope = Base (TCons (_Bool_id, []))
}
let _Bool = TConstr {
  name   = _Bool_id;
  tscope = Base Type;
  constr = [_true; _false]
}

(* Nat *)
let _Nat_id = Id.mk "Nat"
let _O_id = Id.mk "O"
let _S_id = Id.mk "S"
let _O = DConstr {
  name   = _O_id;
  tscope = Base (TCons (_Nat_id, []))
}
let _S = DConstr {
  name   = _S_id;
  tscope = unbox
    (_Bnd (_TCons _Nat_id _nil)
    (_Base (_TCons _Nat_id _nil)))
}
let _Nat = TConstr {
  name = _Nat_id;
  tscope = Base Type;
  constr = [_O; _S]
}