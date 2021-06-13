open Bindlib

type t =
  (* functional *)
  | Var     of t var
  | Ann     of t * ty
  | Type
  | Linear
  | TyProd  of ty * (t, ty) binder
  | LnProd  of ty * (t, ty) binder
  | Lambda  of (t, t) binder
  | App     of t * t
  | LetIn   of t * (t, t) binder
  (* equality *)
  | Eq      of t * t * ty
  | Refl    of t * ty
  | Ind     of ty * t * t * t * t * ty
  (* container *)
  | Tensor  of ty * (t, ty) binder
  | Pair    of t * t
  | LetPair of t * (t, t) mbinder
  | CoProd  of ty * ty
  | InjL    of t
  | InjR    of t
  | Case    of t * (t, t) binder
                 * (t, t) binder
  (* basic *)
  | Unit
  | U
  | Nat
  | Zero
  | Succ    of t
  | Iter    of ty * t * t * t
  (* imperative *)
  | Channel (* Linear *)
  | Open    (* Nat -> Channel *)
  | Close   (* Channel -> Unit *)
  | Read    (* Channel -> Nat * Channel *)
  | Write   (* Nat * Channel -> Channel *)
  | PtsTo   of t * ty (* Nat -> Type -> Linear *)
  | Alloc   (* (A:Type) -> A -> Ptr A *)
  | Free    (* (A:Type) -> Ptr A -> Unit *)
  | Get     (* (A:Type) -> Ptr A -> (A * Ptr A) *)
  | Set     (* (A:Type) -> (A * Ptr A) -> Ptr A *)

and ty = t

type tvar = t var

let mk = new_var (fun x -> Var x)
let __ = mk "_"

let _Var = box_var
let _Ann = box_apply2 (fun t ty -> Ann (t, ty))
let _Type = box Type
let _Linear = box Linear
let _TyProd = box_apply2 (fun ty b -> TyProd (ty, b))
let _LnProd = box_apply2 (fun ty b -> LnProd (ty, b))
let _Arrow ty1 ty2 = _TyProd ty1 (bind_var __ ty2)
let _Lolli ty1 ty2 = _LnProd ty1 (bind_var __ ty2)
let _Lambda = box_apply (fun t -> Lambda t)
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))
let _LetIn = box_apply2 (fun t b -> LetIn (t, b))
let _Eq = box_apply3 (fun t1 t2 ty -> Eq (t1, t2, ty))
let _Refl = box_apply2 (fun t ty -> Refl (t, ty))
let _Ind = 
  let box_apply6 f t1 t2 t3 t4 t5 t6 = 
    apply_box (apply_box (box_apply4 f t1 t2 t3 t4) t5) t6
  in
  box_apply6 (fun p pf t1 t2 eq ty -> Ind (p, pf, t1, t2, eq, ty))
let _Tensor = box_apply2 (fun ty b -> Tensor (ty, b))
let _Tuple ty1 ty2 = _Tensor ty1 (bind_var __ ty2)
let _Pair = box_apply2 (fun t1 t2 -> Pair (t1, t2))
let _LetPair = box_apply2 (fun t mb -> LetPair (t, mb))
let _CoProd = box_apply2 (fun ty1 ty2 -> CoProd (ty1, ty2))
let _InjL = box_apply (fun t -> InjL t)
let _InjR = box_apply (fun t -> InjR t)
let _Case = box_apply3 (fun t b1 b2 -> Case (t, b1, b2))
let _Unit = box Unit
let _U = box U
let _Nat = box Nat
let _Zero = box Zero
let _Succ = box_apply (fun t -> Succ t)
let _Iter = box_apply4 (fun ty t1 t2 t3 -> Iter (ty, t1, t2, t3))
let _Channel = box Channel
let _Open = box Open
let _Close = box Close
let _Read = box Read
let _Write = box Write
let _PtsTo = box_apply2 (fun t ty -> PtsTo (t, ty))
let _Ptr ty =
  let x = mk "x" in
  _Tensor _Nat (bind_var x (_PtsTo (_Var x) ty))
let _Alloc = box Alloc
let _Free = box Free
let _Get = box Get
let _Set = box Set

let rec lift = function
  | Var x -> _Var x
  | Ann (t, ty) -> _Ann (lift t) (lift ty)
  | Type -> _Type
  | Linear -> _Linear
  | TyProd (ty, b) -> _TyProd (lift ty) (box_binder lift b)
  | LnProd (ty, b) -> _LnProd (lift ty) (box_binder lift b)
  | Lambda b -> _Lambda (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)
  | LetIn (t, b) -> _LetIn (lift t) (box_binder lift b)
  | Eq (t1, t2, ty) -> _Eq (lift t1) (lift t2) (lift ty)
  | Refl (t, ty) -> _Refl (lift t) (lift ty)
  | Ind (ty, t1, t2, t3, t4, t5) -> 
    _Ind (lift ty) (lift t1) (lift t2) (lift t3) (lift t4) (lift t5)
  | Tensor (ty, b) -> _Tensor (lift ty) (box_binder lift b)
  | Pair (t1, t2) -> _Pair (lift t1) (lift t2)
  | LetPair (t, mb) -> _LetPair (lift t) (box_mbinder lift mb)
  | CoProd (ty1, ty2) -> _CoProd (lift ty1) (lift ty2)
  | InjL t -> _InjL (lift t)
  | InjR t -> _InjR (lift t)
  | Case (t, b1, b2) -> 
    _Case (lift t) (box_binder lift b1) (box_binder lift b2)
  | Unit -> _Unit
  | U -> _U
  | Nat -> _Nat
  | Zero -> _Zero
  | Succ t -> _Succ (lift t)
  | Iter (ty, t1, t2, t3) -> 
    _Iter (lift ty) (lift t1) (lift t2) (lift t3)
  | Channel -> _Channel
  | Open -> _Open
  | Close -> _Close
  | Read -> _Read
  | Write -> _Write
  | PtsTo (t, ty) -> _PtsTo (lift t) (lift ty)
  | Alloc -> _Alloc
  | Free -> _Free
  | Get -> _Get
  | Set -> _Set

let rec pp fmt = function
  | Var x -> 
    Format.fprintf fmt "%s" (name_of x)
  | Ann (s, t) -> 
    Format.fprintf fmt "@[(%a :@;<1 2>%a)@]" pp s pp t
  | Type -> Format.fprintf fmt "Type"
  | Linear -> Format.fprintf fmt "Linear"
  | TyProd (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then Format.fprintf fmt "@[%a ->@;<1 2>%a@]" pp ty pp b
    else Format.fprintf fmt "@[@[(%s :@;<1 2>%a) ->@]@;<1 2>%a@]"
      (name_of x) pp ty pp b
  | LnProd (ty, b) -> 
    let x, b = unbind b in
    if (name_of x = "_") 
    then Format.fprintf fmt "@[%a >>@;<1 2>%a@]" pp ty pp b
    else Format.fprintf fmt "@[@[(%s :@;<1 2>%a) >>@]@;<1 2>%a@]"
      (name_of x) pp ty pp b
  | Lambda b ->
    let x, b = unbind b in
    Format.fprintf fmt "@[fun %s =>@;<1 2>%a@]"
      (name_of x) pp b
  | App (s, t) ->
    Format.fprintf fmt "@[(%a)@;<1 2>%a@]" pp s pp t
  | LetIn (t, b) -> 
    let x, b = unbind b in
    Format.fprintf fmt "@[@[let %s :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x) pp t pp b
  | Eq (t1, t2, _) ->
    Format.fprintf fmt "@[Eq(%a,@;<1 2>%a)@]" pp t1 pp t2
  | Refl (t, ty) ->
    Format.fprintf fmt "@[refl(%a,@;<1 2> %a)@]" pp t pp ty
  | Ind (p, pf, t1, t2, eq, ty) ->
    Format.fprintf fmt 
      "@[ind(%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a)@]"
      pp p pp pf pp t1 pp t2 pp eq pp ty
  | Tensor (ty, b) ->
    let x, b = unbind b in
    if (name_of x = "_") then
      Format.fprintf fmt "@[(%a *@;<1 2>%a)@]" pp ty pp b
    else
      Format.fprintf fmt "@[(%s : %a *@;<1 2>%a)@]" (name_of x) pp ty pp b
  | Pair (t1, t2) ->
    Format.fprintf fmt "@[(%a, %a)@]" pp t1 pp t2
  | LetPair (t, mb) ->
    let x, mb = unmbind mb in
    let x1 = x.(0) in
    let x2 = x.(1) in
    Format.fprintf fmt "@[@[let (%s, %s) :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]"
      (name_of x1) (name_of x2) pp t pp mb
  | CoProd (ty1, ty2) ->
    Format.fprintf fmt "@[(%a |@;<1 2>%a)@]" pp ty1 pp ty2
  | InjL t -> 
    Format.fprintf fmt "@[(left %a)@]" pp t
  | InjR t -> 
    Format.fprintf fmt "@[(right %a)@]" pp t
  | Case (t, b1, b2) ->
    let x1, b1 = unbind b1 in
    let x2, b2 = unbind b2 in
    Format.fprintf fmt "@[case %a of@;<1; 0> %s => %a@;<1; 0>|%s => %a]"
      pp t (name_of x1) pp b1 (name_of x2) pp b2
  | Unit -> Format.fprintf fmt "@[Unit@]"
  | U -> Format.fprintf fmt "()"
  | Nat -> Format.fprintf fmt "Nat"
  | Zero -> Format.fprintf fmt "0"
  | Succ t -> 
    let rec loop i = function
      | Succ t -> loop (i + 1) t
      | Zero -> Format.fprintf fmt "%d" i
      | t -> Format.fprintf fmt "(%a +1)" pp t
    in
    loop 1 t
  | Iter (p, t1, t2, n) ->
    Format.fprintf fmt 
      "@[iter(%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a)@]"
      pp p pp t1 pp t2 pp n
  | Channel -> Format.fprintf fmt "Channel"
  | Open -> Format.fprintf fmt "open"
  | Close -> Format.fprintf fmt "close"
  | Read -> Format.fprintf fmt "read"
  | Write -> Format.fprintf fmt "write"
  | PtsTo (t, ty) -> 
    Format.fprintf fmt "@[[%a |->@;<1 2>%a]@]" pp t pp ty
  | Alloc -> Format.fprintf fmt "alloc"
  | Free -> Format.fprintf fmt "free"
  | Get -> Format.fprintf fmt "get"
  | Set -> Format.fprintf fmt "set"