open Bindlib
open Terms
open MParser

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let keywords = SSet.of_list [
  "Type";
  "Linear";
  "fun";
  "let";
  "in";
  "Eq";
  "refl";
  "ind";
  "left";
  "right";
  "case";
  "of";
  "Unit";
  "Nat";
  "O";
  "S";
  "iter";
  "Channel";
  "open";
  "close";
  "read";
  "write";
  "alloc";
  "free";
  "get";
  "set";
]

type 'a tparser = ('a, tvar SMap.t) parser

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

let rec var_parser ?pat:(p=false) () =
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
      let* ctx = get_user_state in
      match SMap.find_opt s ctx with
      | Some x -> return x
      | None ->
        let x = mk s in
        let* _ = set_user_state (SMap.add s x ctx) in
        return x)

and sort_parser () = 
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
  let* _ = set_user_state ctx in
  let tyProd = 
    List.fold_right
      (fun x b -> _TyProd ty (bind_var x b)) xs b
  in
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
  let* _ = set_user_state ctx in
  let lnProd = 
    List.fold_right
      (fun x b -> _LnProd ty (bind_var x b)) xs b
  in
  return (lnProd)

and lambda_parser () =
  let* ctx = get_user_state in
  let* _ = kw "fun" in
  let* xs = many1 (var_parser ~pat:true ()) in
  let* _ = kw "=>" in
  let* b = t_parser () in
  let* _ = set_user_state ctx in
  let f = 
    List.fold_right
      (fun x b -> _Lambda (bind_var x b)) xs b
  in
  return f

and letIn_parser () =
  let* ctx = get_user_state in
  let* _ = kw "let" in
  let* x = var_parser ~pat:true () in
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
  return (_LetIn t (bind_var x b))

and eq_parser () =
  let* _ = kw "Eq" in
  let* _ = kw "(" in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw "," in
  let* ty = t_parser () in
  let* _ = kw ")" in
  return (_Eq t1 t2 ty)

and refl_parser () =
  let* _ = kw "refl" in
  let* _ = kw "(" in
  let* t = t_parser () in
  let* _ = kw "," in
  let* ty = t_parser () in
  let* _ = kw ")" in
  return (_Refl t ty)

and ind_parser () =
  let* _ = kw "ind" in
  let* _ = kw "(" in
  let* p = t_parser () in
  let* _ = kw "," in
  let* pf = t_parser () in
  let* _ = kw "," in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw "," in
  let* eq = t_parser () in
  let* _ = kw "," in
  let* ty = t_parser () in
  let* _ = kw ")" in
  return (_Ind p pf t1 t2 eq ty)

and tensor_parser () =
  let* ctx = get_user_state in
  let* _ = kw "(" in
  let* x = var_parser () in
  let* _ = kw ":" in
  let* ty1 = t_parser () in
  let* _ = kw "*" in
  let* ty2 = t_parser () in
  let* _ = kw ")" in
  let* _ = set_user_state ctx in
  return (_Tensor ty1 (bind_var x ty2))

and tuple_parser () =
  let* _ = kw "(" in
  let* ty1 = t_parser () in
  let* _ = kw "*" in
  let* ty2 = t_parser () in
  let* _ = kw ")" in
  return (_Tuple ty1 ty2)

and pair_parser () =
  let* _ = kw "(" in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw ")" in
  return (_Pair t1 t2)

and letPair_parser () =
  let* ctx = get_user_state in
  let* _ = kw "let" in
  let* _ = kw "(" in
  let* x = var_parser ~pat:true () in
  let* _ = kw "," in
  let* y = var_parser ~pat:true () in
  let* _ = kw ")" in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let* _ = kw "in" in
  let* b = t_parser () in
  let* _ = set_user_state ctx in
  return (_LetPair t (bind_mvar [| x; y |] b))

and coProd_parser () =
  let* _ = kw "(" in
  let* ty1 = t_parser () in
  let* _ = kw "|" in
  let* ty2 = t_parser () in
  let* _ = kw ")" in
  return (_CoProd ty1 ty2)

and injL_parser () = 
  let* _ = kw "left" in
  let* t = t_parser () in
  return (_InjL t)

and injR_parser () =
  let* _ = kw "right" in
  let* t = t_parser () in
  return (_InjR t)

and case_parser () =
  let* _ = kw "case" in
  let* t = t_parser () in
  let* _ = kw "of" in
  let* _ = kw "left" in
  let* x1 = var_parser ~pat:true () in
  let* _ = kw "=>" in
  let* b1 = t_parser () in
  let* _ = kw "|" in
  let* _ = kw "right" in
  let* x2 = var_parser ~pat:true () in
  let* _ = kw "=>" in
  let* b2 = t_parser () in
  return (_Case t (bind_var x1 b1) (bind_var x2 b2))

and unit_parser () =
  let* _ = kw "Unit" in
  return _Unit

and u_parser () =
  let* _ = kw "(" in
  let* _ = kw ")" in
  return _U

and nat_parser () =
  let* _ = kw "Nat" in
  return _Nat

and zero_parser () =
  let* _ = kw "O" in
  return _Zero

and succ_parser () =
  let* _ = kw "S" in
  let* t = t_parser () in
  return (_Succ t)

and int_parser () =
  let* s = many1_chars digit in
  let* _ = ws in
  match int_of_string_opt s with
  | Some n ->
    let rec loop i acc =
      if i < n then loop (i + 1) (_Succ acc)
      else acc
    in return (loop 0 _Zero)
  | None -> fail "non-int"

and iter_parser () =
  let* _ = kw "iter" in
  let* _ = kw "(" in
  let* p = t_parser () in
  let* _ = kw "," in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw "," in
  let* n = t_parser () in
  let* _ = kw ")" in
  return (_Iter p t1 t2 n)

and channel_parser () =
  let* _ = kw "Channel" in
  return _Channel

and open_parser () =
  let* _ = kw "open" in
  return _Open

and close_parser () =
  let* _ = kw "close" in
  return _Close

and read_parser () =
  let* _ = kw "read" in
  return _Read

and write_parser () = 
  let* _ = kw "write" in
  return _Write

and ptsTo_parser () =
  let* _ = kw "[" in
  let* n = t_parser () in
  let* _ = kw "|->" in
  let* t = t_parser () in
  let* _ = kw "]" in
  return (_PtsTo n t)

and alloc_parser () =
  let* _ = kw "alloc" in
  return (_Alloc)

and free_parser () =
  let* _ = kw "free" in
  return (_Free)

and get_parser () =
  let* _ = kw "get" in
  return (_Get)

and set_parser () =
  let* _ = kw "set" in
  return (_Set)

and t0_parser () =
  let* _ = return () in
  choice (List.map attempt [
    var_parser () >>= (fun x -> return (_Var x));
    sort_parser ();
    tyProd_parser ();
    lnProd_parser ();
    lambda_parser ();
    letIn_parser ();
    eq_parser ();
    refl_parser ();
    ind_parser ();
    tensor_parser ();
    tuple_parser ();
    pair_parser ();
    letPair_parser ();
    coProd_parser ();
    injL_parser ();
    injR_parser ();
    case_parser ();
    unit_parser ();
    u_parser ();
    nat_parser ();
    zero_parser ();
    succ_parser ();
    int_parser ();
    iter_parser ();
    channel_parser ();
    open_parser ();
    close_parser ();
    read_parser ();
    write_parser ();
    ptsTo_parser ();
    alloc_parser ();
    free_parser ();
    get_parser ();
    set_parser ();
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

let def_parser () =
  let* _ = kw "Definition" in
  let* x = var_parser ~pat:true () in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let* _ = kw "." in
  return (x, _Ann t ty)

let top_parser () =
  let* ts = many1 (def_parser ()) in
  let* ctx = get_user_state in
  let main = _Var (SMap.find "main" ctx) in
  let top = 
    List.fold_right
      (fun (x, t) b -> _LetIn t (bind_var x b)) ts main
  in
  return top

let parse s =
  match parse_string (ws >> top_parser ()) s SMap.empty with
  | Success t -> unbox t
  | Failed (s, _) -> failwith s

let parse_ch ch =
  match parse_channel (ws >> top_parser ()) ch SMap.empty with
  | Success t -> unbox t
  | Failed (s, _) -> failwith s