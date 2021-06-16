open Bindlib
open MParser
open Names
open Terms

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let keywords = SSet.of_list [
  "Definition";
  "Fixpoint";
  "Inductive";
  "Axiom";
  "Type";
  "Linear";
  "fun";
  "fix";
  "let";
  "in";
  "match";
  "as";
  "in";
  "return";
]

type 'a tparser = ('a, t var SMap.t * Id.t SMap.t) parser

let (let*) = bind

let comment = 
  let* _ = string "(*" in
  let* _ = many (
    let* opt =
      (look_ahead (string "*)") >> return None) 
      <|>
      (any_char_or_nl >>= (fun c -> return (Some c)))
    in
    match opt with
    | Some c -> return c
    | None -> zero)
  in
  let* _ = string "*)" in
  return ()

let ws = many (choice [
  blank >> return ();
  newline >> return ();
  comment >> return ();
])

let kw s = 
  let* _ = string s in
  let* _ = ws in
  return ()

let parens p =
  let* _ = kw "(" in
  let* t = p in
  let* _ = kw ")" in
  return t

let var_parser ?pat:(p=false) () : t var tparser =
  let* s1 = many1_chars (letter <|> char '_') in
  let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
  let* _ = ws in
  let s = s1 ^ s2 in
  if s = "_" then 
    if p then return __ else fail "non pattern variable"
  else
    match SSet.find_opt s keywords with
    | Some _ -> fail (Printf.sprintf "not a valid variable name(%s)" s)
    | None -> (
      let* (v_ctx, id_ctx) = get_user_state in
      match SMap.find_opt s v_ctx with
      | Some x -> return x
      | None ->
        let x = mk s in
        let* _ = set_user_state (SMap.add s x v_ctx, id_ctx) in
        return x)

let id_parser : Id.t tparser =
  let* s1 = many1_chars (letter <|> char '_') in
  let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
  let* _ = ws in
  let s = s1 ^ s2 in
  if s = "_" then fail "non pattern variable"
  else
    match SSet.find_opt s keywords with
    | Some _ -> fail (Printf.sprintf "not a valid id name(%s)" s)
    | None -> (
      let* (v_ctx, id_ctx) = get_user_state in
      match SMap.find_opt s id_ctx with
      | Some x -> return x
      | None ->
        let x = Id.mk s in
        let* _ = set_user_state (v_ctx, SMap.add s x id_ctx) in
        return x)

let rec p_parser ?is_type:(p=false) () : p tparser = 
  (var_parser ~pat:true () >>= fun x -> return (PVar x))
  <|>
  let* id = id_parser in
  let* opt = option (
    let* _ = kw "(" in
    let* ps = sep_by (p_parser ()) (kw ",") in
    let* _ = kw ")" in
    return ps)
  in
  let ps =
    match opt with
    | Some ps -> ps
    | None -> []
  in
  if p then return (PTCons (id, ps))
  else return (PDCons (id, ps))

let rec sort_parser () = 
  (let* _ = kw "Type" in return _Type)
  <|>
  (let* _ = kw "Linear" in return _Linear)

and tyProd_parser () =
  let* ctx = get_user_state in
  let* _ = kw "(" in
  let* xs = many1 (var_parser ()) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw ")" in
  let* _ = kw "->" in
  let* b = t_parser () in
  let tyProd = 
    List.fold_right
      (fun x b -> _TyProd ty (bind_var x b)) xs b
  in
  let* _ = set_user_state ctx in
  return (tyProd)

and lnProd_parser () =
  let* ctx = get_user_state in
  let* _ = kw "(" in
  let* xs = many1 (var_parser ()) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw ")" in
  let* _ = kw ">>" in
  let* b = t_parser () in
  let lnProd = 
    List.fold_right
      (fun x b -> _LnProd ty (bind_var x b)) xs b
  in
  let* _ = set_user_state ctx in
  return (lnProd)

and lambda_parser () =
  let* ctx = get_user_state in
  let* _ = kw "fun" in
  let* xs = many1 (p_parser ()) in
  let* _ = kw "=>" in
  let* t = t_parser () in
  let f = 
    List.fold_right
      (fun x t -> _Lambda (bind_p x t)) xs t
  in
  let* _ = set_user_state ctx in
  return f

and fix_parser () =
  let* ctx = get_user_state in
  let* _ = kw "fix" in
  let* x = var_parser () in
  let* xs = many1 (p_parser ()) in
  let* _ = kw "=>" in
  let* t = t_parser () in
  let f = 
    List.fold_right
      (fun x t -> _Lambda (bind_p x t)) xs t
  in
  let* _ = set_user_state ctx in
  return (_Fix (bind_var x f))

and letIn_parser () =
  let* ctx = get_user_state in
  let* _ = kw "let" in
  let* x = p_parser () in
  let* opt = option (attempt (kw ":" >> t_parser ())) in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let t = 
    match opt with
    | Some ty -> _Ann t ty
    | None -> t
  in
  let* _ = kw "in" in
  let* b = t_parser () in
  let* _ = set_user_state ctx in
  return (_LetIn t (bind_p x b))

and tcons_parser () =
  let* id = id_parser in
  let* opt = option (
    let* _ = kw "(" in
    let* ts = sep_by (t_parser ()) (kw ",") in
    let* _ = kw ")" in
    return ts)
  in
  let ts =
    match opt with
    | Some ts -> ts
    | None -> []
  in
  return (_TCons id (box_of_list ts))

and dcons_parser () =
  let* id = id_parser in
  let* opt = option (
    let* _ = kw "(" in
    let* ts = sep_by (t_parser ()) (kw ",") in
    let* _ = kw ")" in
    return ts)
  in
  let ts =
    match opt with
    | Some ts -> ts
    | None -> []
  in
  return (_DCons id (box_of_list ts))

and match_parser () =
  let* _ = kw "match" in
  let* t = t_parser () in
  let* opt = option (motive_parser ()) in
  let m =
    match opt with
    | Some m -> m
    | None -> _None
  in
  let* _ = kw "with" in
  let* cls = many (clause_parser ()) in
  let* _ = kw "end" in
  return (_Match t m (box_of_list cls))

and motive_parser () =
  let* opt = option (
    let* _ = kw "as" in
    let* x = var_parser () in
    return x)
  in
  let x = 
    match opt with
    | Some x -> x
    | None -> __
  in
  let* _ = kw "in" in
  let* p = p_parser ~is_type:true () in
  let* _ = kw "return" in
  let* t = t_parser () in
  return (_Some (bind_var x (bind_p p t)))

and clause_parser () =
  let* _ = kw "|" in
  let* p = p_parser () in
  let* _ = kw "=>" in
  let* t = t_parser () in
  return (bind_p p t)

and t0_parser () =
  let* _ = return () in
  choice (List.map attempt [
    var_parser () >>= (fun x -> return (_Var x));
    sort_parser ();
    tyProd_parser ();
    lnProd_parser ();
    lambda_parser ();
    letIn_parser ();
    tcons_parser ();
    dcons_parser ();
    match_parser ();
    parens (t_parser ())
  ])

and t1_parser () =
  let* _ = return () in
  let* t = t0_parser () in
  let* ts = many (t0_parser ()) in
  let t = List.fold_left 
    (fun t1 t2 -> _App t1 t2) t ts   
  in
  return t

and t2_parser () =
  let arrow_parser () =
    let* _ = kw "->" in
    return (fun ty1 ty2 -> _Arrow ty1 ty2)
  in
  let lolli_parser () =
    let* _ = kw ">>" in
    return (fun ty1 ty2 -> _Lolli ty1 ty2)
  in
  let* t = chain_right1 (t1_parser ()) 
    (arrow_parser () <|> lolli_parser ())
  in
  return t

and t_parser () = 
  attempt (t2_parser ())
  <|>
  let* _ = kw "(" in
  let* t = t2_parser () in
  let* _ = kw ":" in
  let* ty = t2_parser () in
  let* _ = kw ")" in
  return (_Ann t ty)

let param_parser =
  let* _ = kw "(" in
  let* x = var_parser ~pat:true () in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw ")" in
  return (x, ty)

let rec definition_parser () =
  let* _ = kw "Definition" in
  let* x = var_parser ~pat:true () in
  let* ctx = get_user_state in
  let* ps = many (param_parser) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let ty =
    List.fold_right
      (fun (x, ty) acc -> 
        _TyProd ty (bind_var x acc)) ps ty 
  in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let t =
    List.fold_right
      (fun (x, _) acc -> 
        _Lambda (bind_p (PVar x) acc) ) ps t
  in
  let* _ = kw "." in
  let* _ = set_user_state ctx in
  let* tp = top_parser () in
  return (_Define (_Ann t ty) (bind_var x tp))

and fixpoint_parser () =
  let* _ = kw "Fixpoint" in
  let* x = var_parser () in
  let* ctx = get_user_state in
  let* ps = many (param_parser) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let ty =
    List.fold_right
      (fun (x, ty) acc -> 
        _TyProd ty (bind_var x acc)) ps ty 
  in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let t =
    _Fix (bind_var x
      (List.fold_right
        (fun (x, _) acc -> 
          _Lambda (bind_p (PVar x) acc) ) ps t))
  in
  let* _ = kw "." in
  let* _ = set_user_state ctx in
  let* tp = top_parser () in
  return (_Define (_Ann t ty) (bind_var x tp))

and datype_parser () =
  let* _ = kw "Inductive" in
  let* id = id_parser in
  let* _ = kw ":" in
  let* ts = tscope_parser () in
  let* _ = kw ":=" in
  let* cstr = many (constr_parser ()) in
  let* _ = kw "." in
  let* tp = top_parser () in
  return (_Datype (_TConstr id ts (box_list cstr)) tp)

and constr_parser () =
  let* _ = kw "|" in
  let* id = id_parser in
  let* _ = kw ":" in
  let* ts = tscope_parser () in
  return (_DConstr id ts)

and base_parser () =
  let* t = t_parser () in
  return (_Base t)

and bind_parser () =
  let* ctx = get_user_state in
  let* _ = kw "(" in
  let* xs = many1 (var_parser ()) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw ")" in
  let* _ = kw "->" in
  let* b = tscope_parser () in
  let bnd = 
    List.fold_right
      (fun x b -> _Bind ty (bind_var x b)) xs b
  in
  let* _ = set_user_state ctx in
  return bnd

and tscope_parser () =  
  choice [
    bind_parser ();
    base_parser ();
  ]

and axiom_parser () =
  let* _ = kw "Axiom" in
  let* x = var_parser () in
  let id = Id.mk (name_of x) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw "." in
  let* tp = top_parser () in
  return (_Define (_Axiom id ty) (bind_var x tp))

and top_parser () =
  choice [
    definition_parser ();
    fixpoint_parser ();
    datype_parser ();
    axiom_parser ();
  ]

let parse s =
  let ctx = (SMap.empty, SMap.empty) in
  match parse_string (ws >> top_parser ()) s ctx with
  | Success t -> unbox t
  | Failed (s, _) -> failwith s

let parse_ch ch =
  let ctx = (SMap.empty, SMap.empty) in
  match parse_channel (ws >> top_parser ()) ch ctx with
  | Success t -> unbox t
  | Failed (s, _) -> failwith s