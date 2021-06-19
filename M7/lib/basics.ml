open Pparser
let basic = parse "
  Inductive Eq (A : Type) (x : A) : A -> Type :=
  | refl : Eq A x x.

  Definition eq_sym 
    (A : Type) 
    (x y : A) 
    (e : Eq A x y) :
    Eq A y x
  :=
    match e in Eq _ _ y return Eq A y x with
    | refl => refl
    end.

  Definition TyInd 
    (A : Type) 
    (x : A)
    (y : A)
    (P : A -> Type) 
    (e : Eq A x y)
    (f : P x) :
    P y
  := 
    match e in Eq _ _ y return P y with
    | refl => f
    end.

  Definition LnInd 
    (A : Type) 
    (x : A)
    (y : A)
    (P : A -> Linear) 
    (e : Eq A x y)
    (f : P x) :
    P y
  := 
    match e in Eq _ _ y return P y with
    | refl => f
    end.

  Inductive Unit : Type :=
  | tt : Unit.

  Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

  Inductive Bool : Type :=
  | true : Bool
  | false : Bool.

  Inductive Sigma (A : Type) (F : A -> Type) : Type :=
  | pair : (x : A) -> F x -> Sigma A F.

  Inductive Tensor (A : Linear) (B : Linear) : Linear :=
  | tpair : A -> B -> Tensor A B.

  Inductive FTensor (A : Type) (F : A -> Linear) : Linear :=
  | fpair : (x : A) -> F x -> FTensor A F.

  Definition Loc : Type := Nat.
  Axiom PtsTo : Loc -> Type -> Linear.
  Definition Ptr (A : Type) : Linear := FTensor Loc (fun l => PtsTo l A).
  Axiom New  : (A : Type) -> A -> Ptr A.
  Axiom Free : (A : Type) -> Ptr A -> Unit.
  Axiom Get  : (A : Type) -> (l : Loc) -> PtsTo l A -> FTensor A (fun _ => PtsTo l A).
  Axiom Set  : (A : Type) -> (B : Type) -> B -> (l : Loc) -> PtsTo l A -> PtsTo l B.
"

let v_ctx, id_ctx = snd basic

let _tt = SMap.find "tt" id_ctx
let _O = SMap.find "O" id_ctx
let _S = SMap.find "S" id_ctx
let _Sigma = SMap.find "Sigma" id_ctx
let _pair = SMap.find "pair" id_ctx
let _Tensor = SMap.find "Tensor" id_ctx
let _FTensor = SMap.find "FTensor" id_ctx
let _tpair = SMap.find "tpair" id_ctx
let _fpair = SMap.find "fpair" id_ctx
let _PtsTo = SMap.find "PtsTo" v_ctx
let _New = SMap.find "New" v_ctx
let _Free = SMap.find "Free" v_ctx
let _Get = SMap.find "Get" v_ctx
let _Set = SMap.find "Set" v_ctx