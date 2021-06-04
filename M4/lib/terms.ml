open Bindlib

type m =
  | I (* intuitionistic *)
  | L (* linear *)

type t =
  (* variable and annotation *)
  | Var         of t var                 (* infer *)
  | Ann         of t * ty                (* infer *)
  (* functional *)
  | Type        of m                     (* infer *)
  | Prod        of ty * (ty, ty) binder  (* infer *)
  | Lolli       of ty * ty               (* infer *)
  | Lambda      of (t, t) binder         (* check *)
  | App         of t * t                 (* infer *)
  | LetIn       of t * (t, t) binder     (* infer *)
  (* equality *)
  | Eq          of t * t * ty            (* infer *)
  | Refl        of t * ty                (* infer *)
  | Ind         of ty * t * t * t * t    (* infer *)
  (* natural numbers *)
  | Nat                                  (* infer *)
  | Zero                                 (* infer *)
  | Succ        of t                     (* infer *)
  | Nat_elim    of ty * t * t * t        (* infer *)
  (* modality *)
  | G           of ty                    (* infer *)
  | G_intro     of t                     (* infer *)
  | G_elim      of t                     (* infer *)
  | F           of ty * (ty, ty) binder  (* infer *)
  | F_intro     of t * t                 (* check *)
  | F_elim      of t * (t, t) mbinder    (* infer *)
  (* unit data *)
  | Unit        of m                     (* infer *)
  | True                                 (* infer *)
  | U                                    (* check *)
  | Unit_elim   of t * t                 (* infer *)
  (* tuple data *)
  | Sum         of ty * (ty, ty) binder  (* infer *)
  | Tensor      of ty * ty               (* infer *)
  | And         of ty * ty               (* infer *)
  | Pair        of t * t                 (* check *)
  | Proj1       of t                     (* infer *)
  | Proj2       of t                     (* infer *)
  | Tensor_elim of t * (t, t) mbinder    (* infer *)
  (* magic *)
  | Axiom       of ty * (ty, t) binder   (* infer *)

and ty = t

type tvar = t var

let __ = new_var (fun x -> Var x) "_"
let mk = new_var (fun x -> Var x)

let _Var = box_var
let _Ann = box_apply2 (fun t ty -> Ann (t, ty))
let _Type m = box (Type m)
let _Prod = box_apply2 (fun ty b -> Prod (ty, b))
let _Arrow ty1 ty2 =
  let ty2 = bind_var __ ty2 in
  _Prod ty1 ty2
let _Lolli = box_apply2 (fun ty1 ty2 -> Lolli (ty1, ty2))
let _Lambda = box_apply (fun b -> Lambda b)
let _Const t =
  let t = bind_var __ t in
  _Lambda t
let _App = box_apply2 (fun t1 t2 -> App (t1, t2))
let _mApp f args = 
  List.fold_left
    (fun f arg -> _App f arg) f args
let _LetIn = box_apply2 (fun t b -> LetIn (t, b))
let _Eq = box_apply3 (fun t1 t2 ty -> Eq (t1, t2, ty))
let _Refl = box_apply2 (fun t ty -> Refl (t, ty))
let _Ind = 
  let box_apply5 f t1 t2 t3 t4 t5 = apply_box (box_apply4 f t1 t2 t3 t4) t5 in
  box_apply5 (fun p pf t1 t2 eq -> Ind (p, pf, t1, t2, eq))
let _Nat = box Nat
let _Zero = box Zero
let _Succ = box_apply (fun t -> Succ t)
let _Nat_elim = 
  box_apply4 (fun p t1 t2 n -> Nat_elim (p, t1, t2, n)) 
let _G = box_apply (fun ty -> G ty)
let _G_intro = box_apply (fun t -> G_intro t)
let _G_elim = box_apply (fun t -> G_intro t)
let _F = box_apply2 (fun ty b -> F (ty, b))
let _F_intro = box_apply2 (fun t1 t2 -> F_intro (t1, t2))
let _F_elim = box_apply2 (fun t mb -> F_elim (t, mb))
let _Sum = box_apply2 (fun ty b -> Sum (ty, b))
let _Tuple ty1 ty2 = 
  let ty2 = bind_var __ ty2 in
  box_apply2 (fun ty b -> Sum (ty, b)) ty1 ty2
let _Tensor = box_apply2 (fun ty1 ty2 -> Tensor (ty1, ty2))
let _And = box_apply2 (fun ty1 ty2 -> And (ty1, ty2))
let _Pair = box_apply2 (fun t1 t2 -> Pair (t1, t2))
let _Proj1 = box_apply (fun t -> Proj1 t)
let _Proj2 = box_apply (fun t -> Proj2 t)
let _Tensor_elim = box_apply2 (fun t mb -> Tensor_elim (t, mb))
let _Unit m = box (Unit m)
let _True = box True
let _U = box U
let _Unit_elim = box_apply2 (fun t1 t2 -> Unit_elim (t1, t2))
let _Axiom = box_apply2 (fun ty b -> Axiom (ty, b))

let rec lift = function
  | Var x -> _Var x
  | Ann (t, ty) -> _Ann (lift t) (lift ty)
  | Type m -> _Type m
  | Prod (ty, b) -> _Prod (lift ty) (box_binder lift b)
  | Lolli (ty1, ty2) -> _Lolli (lift ty1) (lift ty2)
  | Lambda b -> _Lambda (box_binder lift b)
  | App (t1, t2) -> _App (lift t1) (lift t2)
  | LetIn (t, b) -> _LetIn (lift t) (box_binder lift b)
  | Eq (t1, t2, ty) -> _Eq (lift t1) (lift t2) (lift ty)
  | Refl (t, ty) -> _Refl (lift t) (lift ty)
  | Ind (ty, pf, t1, t2, eq) -> 
    _Ind (lift ty) (lift pf) (lift t1) (lift t2) (lift eq)
  | Nat -> _Nat
  | Zero -> _Zero
  | Succ t -> _Succ (lift t)
  | Nat_elim (p, t1, t2, n) ->
    _Nat_elim (lift p) (lift t1) (lift t2) (lift n)
  | G ty -> _G (lift ty)
  | G_intro t -> _G_intro (lift t)
  | G_elim t -> _G_elim (lift t)
  | F (ty, b) -> _F (lift ty) (box_binder lift b)
  | F_intro (t1, t2) -> _F_intro (lift t1) (lift t2)
  | F_elim (t, b) -> _F_elim (lift t) (box_mbinder lift b)
  | Sum (ty, b) -> _Sum (lift ty) (box_binder lift b)
  | Tensor (ty1, ty2) -> _Tensor (lift ty1) (lift ty2)
  | And (ty1, ty2) -> _And (lift ty1) (lift ty2)
  | Pair (t1, t2) -> _Pair (lift t1) (lift t2)
  | Proj1 t -> _Proj1 (lift t)
  | Proj2 t -> _Proj2 (lift t)
  | Tensor_elim (t, mb) -> _Tensor_elim (lift t) (box_mbinder lift mb)
  | Unit m -> _Unit m
  | True -> _True
  | U -> _U
  | Unit_elim (t1, t2) -> _Unit_elim (lift t1) (lift t2)
  | Axiom (ty, b) -> _Axiom (lift ty) (box_binder lift b)

let rec pp fmt = function
  | Var x -> 
    Format.fprintf fmt "%s" (name_of x)
  | Ann (t, ty) -> 
    Format.fprintf fmt "(%a) : %a" pp t pp ty
  | Type m -> (
    match m with
    | I -> Format.fprintf fmt "Type"
    | L -> Format.fprintf fmt "Linear")
  | Prod (ty, b) ->
    let x, b = unbind b in
    if (eq_vars x __) 
    then Format.fprintf fmt "@[(%a ->@;<1 2>%a)@]" pp ty pp b
    else Format.fprintf fmt "@[@[forall (%s :@;<1 2>%a),@]@;<1 2>%a@]" 
      (name_of x) pp ty pp b
  | Lolli (ty1, ty2) ->
    Format.fprintf fmt "@[(%a -o@;<1 2>%a)@]" pp ty1 pp ty2
  | Lambda b ->
    let x, b = unbind b in
    Format.fprintf fmt "@[fun %s =>@;<1 2>%a@]" (name_of x) pp b
  | App (t1, t2) ->
    Format.fprintf fmt "@[(%a) %a@]" pp t1 pp t2
  | LetIn (t, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "@[let %s := %a in@;<1 0>%a@]" 
      (name_of x) pp t pp b
  | Eq (t1, t2, _) ->
    Format.fprintf fmt "@[%a ===@;<1 2>%a@]" pp t1 pp t2
  | Refl (t, ty) ->
    Format.fprintf fmt "(refl %a %a)" pp t pp ty
  | Ind (p, pf, t1, t2, eq) ->
    Format.fprintf fmt 
      "@[ind (%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a)@]"
      pp p pp pf pp t1 pp t2 pp eq
  | Nat -> Format.fprintf fmt "Nat"
  | Zero -> Format.fprintf fmt "0"
  | Succ t -> 
    let rec loop i = function
      | Succ t -> loop (i + 1) t
      | Zero -> Format.fprintf fmt "%d" i
      | t -> Format.fprintf fmt "(%a +1)" pp t
    in
    loop 1 t
  | Nat_elim (p, t1, t2, n) ->
    Format.fprintf fmt 
      "@[ind (%a,@;<1 2>%a,@;<1 2>%a,@;<1 2>%a)@]"
      pp p pp t1 pp t2 pp n
  | G ty ->
    Format.fprintf fmt "@[(Pack %a)@]" pp ty
  | G_intro t ->
    Format.fprintf fmt "@[(pack %a)@]" pp t
  | G_elim t ->
    Format.fprintf fmt "@[(unpack %a)@]" pp t
  | F (ty, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "@[@[F (%s : %a),@]@;<1 2>%a@]" 
      (name_of x) pp ty pp b
  | F_intro (t1, t2) ->
    Format.fprintf fmt "F (%a, %a)" pp t1 pp t2
  | F_elim (t, mb) ->
    let mx, b = unmbind mb in
    let x1, x2 = (mx.(0), mx.(1)) in
    Format.fprintf fmt "@[let F (%s, %s) := %a in@;<1 0>%a@]"
      (name_of x1) (name_of x2) pp t pp b
  | Sum (ty, b) ->
    let x, b = unbind b in
    if (eq_vars x __) 
    then Format.fprintf fmt "@[(%a *@;<1 2>%a)@]" pp ty pp b
    else Format.fprintf fmt "@[@[exists (%s : %a),@]@;<1 2>%a@]"
      (name_of x) pp ty pp b
  | Tensor (ty1, ty2) ->
    Format.fprintf fmt "@[(%a ^@;<1 2>%a)@]" pp ty1 pp ty2
  | And (ty1, ty2) ->
    Format.fprintf fmt "@[(%a &@;<1 2>%a)@]" pp ty1 pp ty2
  | Pair (t1, t2) ->
    Format.fprintf fmt "@[(%a,@;<1 2>%a)@]" pp t1 pp t2
  | Proj1 t ->
    Format.fprintf fmt "(%a).1" pp t
  | Proj2 t ->
    Format.fprintf fmt "(%a).2" pp t
  | Tensor_elim (t, mb) ->
    let mx, b = unmbind mb in
    let x1, x2 = (mx.(0), mx.(1)) in
    Format.fprintf fmt "@[let (%s, %s) := %a in@;<1 0>%a@]"
      (name_of x1) (name_of x2) pp t pp b
  | Unit m -> (
    match m with
    | I -> Format.fprintf fmt "unit"
    | L -> Format.fprintf fmt "null")
  | True -> Format.fprintf fmt "True"
  | U -> Format.fprintf fmt "()"
  | Unit_elim (t1, t2) ->
    Format.fprintf fmt "@[let () := %a in@;<1 0>%a@]" pp t1 pp t2
  | Axiom (ty, b) ->
    let x, b = unbind b in
    Format.fprintf fmt "@[axiom %s : %a in@;<1 0>%a@]"
      (name_of x) pp ty pp b
    