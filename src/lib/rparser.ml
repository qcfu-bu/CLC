open Format
open MParser
open Util
open Names
open Basics
open Raw

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let keywords = SSet.of_list [
  "Definition";
  "Fixpoint";
  "Inductive";
  "Axiom";
  "U";
  "L";
  "fun";
  "fix";
  "let";
  "in";
  "match";
  "as";
  "in";
  "return";
  "with";
  "end";
]

type 'a tparser = ('a, Name.t SMap.t * Id.t SMap.t) parser

let (let*) = bind

let rec repeatn p n =
  if n <= 0 then return []
  else
    let* x = p in
    let* xs = repeatn p (n - 1) in
    return (x :: xs)

let any = any_char_or_nl >> return ()

let rec comment () : unit tparser = 
  let* _ = string "(*" in
  let* _ = many (
    let* opt =
      (look_ahead (string "*)") >> return true) 
      <|>
      ((comment () <|> any) >> return false)
    in
    if opt then zero
    else return ())
  in
  let* _ = string "*)" in
  return ()

and ws () = 
  many (choice [
    (blank >> return ());
    (newline >> return ());
    (comment ()); 
  ]) >> return ()

let kw s = 
  let* _ = string s in
  let* _ = ws () in
  return ()

let parens p =
  let* _ = kw "(" in
  let* t = p in
  let* _ = kw ")" in
  return t

let var_parser ?pat:(p=false) () =
  let* s1 = many1_chars (letter <|> char '_') in
  let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
  let* _ = ws () in
  let s = s1 ^ s2 in
  if s = "_" then 
    if p then return Name.__ else zero
  else
    match SSet.find_opt s keywords with
    | Some _ -> fail (Printf.sprintf "not a valid variable name(%s)" s)
    | None -> (
      let* (v_ctx, id_ctx) = get_user_state in
      match SMap.find_opt s v_ctx with
      | Some x -> return x
      | None ->
        let x = Name.mk s in
        let* _ = set_user_state (SMap.add s x v_ctx, id_ctx) in
        return x)

let meta_parser () =
  let* _ = kw "_" in
  return (Meta.mk ())

let id_parser ?intro:(p=false) ?tcons:(t=false) ?arity:(n=0) ()  =
  let* s1 = many1_chars (letter <|> char '_') in
  let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
  let* _ = ws () in
  let s = s1 ^ s2 in
  if s = "_" then fail "non pattern variable"
  else
    match SSet.find_opt s keywords with
    | Some _ -> zero
    | None -> (
      let* (v_ctx, id_ctx) = get_user_state in
      match SMap.find_opt s id_ctx with
      | Some x -> return x
      | None ->
        if p then
          let x = Id.mk s ~tcons:t ~arity:n () in
          let* _ = set_user_state (v_ctx, SMap.add s x id_ctx) in
          return x
        else fail (sprintf "undefined id(%s)" s))

let rec pvar_parser () =
  let* x = var_parser ~pat:true () in 
  return (PVar x)

and pcons_parser () =
  let* id = id_parser () in
  let n = Id.get_arity id in
  let* ps = repeatn (p_parser ()) n in
  if Id.get_tcons id 
  then return (PTCons (id, ps))
  else return (PDCons (id, ps))

and p_tt_parser () =
  let* _ = kw "(" in
  let* _ = kw ")" in
  return (PDCons (_tt, []))

and p_ftensor_parser () =
  let* _ = kw "[" in
  let* p1 = p_parser () in
  let* _ = kw "|" in
  let* p2 = p_parser () in
  let* _ = kw "]" in
  return (PTCons (_FTensor, [p1; p2]))

and p_pair_parser () =
  let* _ = kw "(" in
  let* p1 = p_parser () in
  let* _ = kw "," in
  let* p2 = p_parser () in
  let* _ = kw ")" in
  return (PDCons (_pair, [p1; p2]))

and p_fpair_parser () =
  let* _ = kw "[" in
  let* p1 = p_parser () in
  let* _ = kw "," in
  let* p2 = p_parser () in
  let* _ = kw "]" in
  return (PDCons (_fpair, [p1; p2]))

and p_tpair_parser () =
  let* _ = kw "{" in
  let* p1 = p_parser () in
  let* _ = kw "," in
  let* p2 = p_parser () in
  let* _ = kw "}" in
  return (PDCons (_tpair, [p1; p2]))

and p0_parser () = 
  let* _ = return () in
  choice (List.map attempt [
    pcons_parser (); 
    pvar_parser ();
    p_tt_parser();
    p_ftensor_parser ();
    p_pair_parser ();
    p_fpair_parser ();
    p_tpair_parser ();
    parens (p_parser ());
  ])

and p_parser () =
  let prod_parser =
   (let* _ = kw "*" in
    return (fun p1 p2 -> PTCons (_Sigma, [p1; p2])))
    <|>
   (let* _ = kw "^" in
    return (fun p1 p2 -> PTCons (_Tensor, [p1; p2])))
  in
  chain_left1 (p0_parser ()) prod_parser

let rec sort_parser () = 
  (let* _ = kw "U" in return U)
  <|>
  (let* _ = kw "L" in return L)

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
      (fun x b -> Arrow (x, ty, b)) xs b
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
  let* _ = kw "-o" in
  let* b = t_parser () in
  let lnProd = 
    List.fold_right
      (fun x b -> Lolli (x, ty, b)) xs b
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
      (fun x t -> Lambda (x, t)) xs t
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
      (fun x t -> Lambda (x, t)) xs t
  in
  let* _ = set_user_state ctx in
  return (Fix (x, f))

and letIn_parser () =
  let* ctx = get_user_state in
  let* _ = kw "let" in
  let* x = p_parser () in
  let* opt = option (attempt (kw ":" >> t_parser ())) in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let t = 
    match opt with
    | Some ty -> Ann (t, ty)
    | None -> t
  in
  let* _ = kw "in" in
  let* b = t_parser () in
  let* _ = set_user_state ctx in
  return (LetIn (x, t, b))

and cons_parser () =
  let* id = id_parser () in
  let n = Id.get_arity id in
  let* ts = repeatn (t0_parser ()) n in
  if Id.get_tcons id 
  then return (TCons (id, ts))
  else return (DCons (id, ts))

and match_parser () =
  let* _ = kw "match" in
  let* t = t_parser () in
  let* opt = option (attempt (motive_parser ())) in
  let m =
    match opt with
    | Some m -> m
    | None -> None
  in
  let* _ = kw "with" in
  let* cls = many (clause_parser ()) in
  let* _ = kw "end" in
  return (Match (t, m, cls))

and motive_parser () =
  let* opt = option (
    let* _ = kw "as" in
    let* x = var_parser () in
    return x)
  in
  let x = 
    match opt with
    | Some x -> x
    | None -> Name.__
  in
  let* _ = kw "in" in
  let* p = p_parser () in
  let* _ = kw "return" in
  let* t = t_parser () in
  return (Some (x, p, t))

and clause_parser () =
  let* _ = kw "|" in
  let* p = p_parser () in
  let* _ = kw "=>" in
  let* t = t_parser () in
  return (p, t)

and tt_parser () =
  let* _ = kw "(" in
  let* _ = kw ")" in
  return (DCons (_tt, []))

and sigma_parser () =
  let* _ = kw "(" in
  let* x = var_parser () in
  let* _ = kw ":" in
  let* ty1 = t_parser () in
  let* _ = kw "|" in
  let* ty2 = t_parser () in
  let* _ = kw ")" in
  return (TCons (_Sigma, [ty1; Lambda (PVar x, ty2)]))

and ftensor_parser () =
  let* _ = kw "[" in
  let* x = var_parser () in
  let* _ = kw ":" in
  let* ty1 = t_parser () in
  let* _ = kw "|" in
  let* ty2 = t_parser () in
  let* _ = kw "]" in
  return (TCons (_FTensor, [ty1; Lambda (PVar x, ty2)]))

and fprod_parser () =
  let* _ = kw "[" in
  let* ty1 = t_parser () in
  let* _ = kw "|" in
  let* ty2 = t_parser () in
  let* _ = kw "]" in
  return (TCons (_FTensor, [ty1; Lambda (PVar Name.__, ty2)]))

and pair_parser () =
  let* _ = kw "(" in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw ")" in
  return (DCons (_pair, [t1; t2]))

and fpair_parser () =
  let* _ = kw "[" in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw "]" in
  return (DCons (_fpair, [t1; t2]))

and tpair_parser () =
  let* _ = kw "{" in
  let* t1 = t_parser () in
  let* _ = kw "," in
  let* t2 = t_parser () in
  let* _ = kw "}" in
  return (DCons (_tpair, [t1; t2]))

and int_parser () =
  let* s = many1_chars digit in
  let* _ = ws () in
  match int_of_string_opt s with
  | Some n ->
    let rec loop i acc =
      if i < n then loop (i + 1) (DCons (_S, [acc]))
      else acc
    in return (loop 0 (DCons (_O, [])))
  | None -> fail "non-int"

and t0_parser () =
  let* _ = return () in
  choice (List.map attempt [
    cons_parser ();
    var_parser () >>= (fun x -> return (Var x));
    meta_parser () >>= (fun x -> return (Meta x));
    sort_parser ();
    lambda_parser ();
    letIn_parser ();
    match_parser ();
    tt_parser ();
    sigma_parser ();
    ftensor_parser ();
    fprod_parser ();
    pair_parser ();
    fpair_parser ();
    tpair_parser ();
    int_parser ();
    parens (t_parser ())
  ])

and t1_parser () =
  let* _ = return () in
  choice (List.map attempt [
    t0_parser ();
    tyProd_parser ();
    lnProd_parser ();
  ])

and t2_parser () =
  let* _ = return () in
  let* t = t1_parser () in
  let* ts = many (t1_parser ()) in
  let t = List.fold_left 
    (fun t1 t2 -> App (t1, t2)) t ts   
  in
  return t

and t3_parser () =
  let prod_parser =
   (let* _ = kw "*" in
    let p = PVar Name.__ in
    return (fun ty1 ty2 -> TCons (_Sigma, [ty1; Lambda (p, ty2)])))
    <|>
   (let* _ = kw "^" in
    return (fun ty1 ty2 -> TCons (_Tensor, [ty1; ty2])))
  in
  chain_left1 (t2_parser ()) prod_parser

and t4_parser () =
  let at_parser =
   (let* _ = kw "+" in
    return (fun t1 t2 -> App (App (Var (_add), t1), t2)))
  in
  chain_left1 (t3_parser ()) at_parser

and t5_parser () =
  let at_parser =
   (let* _ = kw "@" in
    return (fun ty loc -> App (App (Var (_PtsTo), loc), ty)))
  in
  chain_left1 (t4_parser ()) at_parser

and t6_parser () =
  let arrow_parser () =
    let* _ = kw "->" in
    return (fun ty1 ty2 -> Arrow (Name.__, ty1, ty2))
  in
  let lolli_parser () =
    let* _ = kw "-o" in
    return (fun ty1 ty2 -> Lolli (Name.__, ty1, ty2))
  in
  chain_right1 (t5_parser ())
    (arrow_parser () <|> lolli_parser ())

and t_parser () = 
  attempt (t6_parser ())
  <|>
  let* _ = kw "(" in
  let* t = t6_parser () in
  let* _ = kw ":" in
  let* ty = t6_parser () in
  let* _ = kw ")" in
  return (Ann (t, ty))

let param_parser =
  let* _ = kw "(" in
  let* xs = many1 (var_parser ~pat:true ()) in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw ")" in
  return (xs, ty)

let rec definition_parser () =
  let* _ = kw "Definition" in
  let* x = var_parser ~pat:true () in
  let* ctx = get_user_state in
  let* ps = many param_parser in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let ty =
    List.fold_right (fun (xs, ty) acc -> 
        List.fold_right (fun x acc -> 
          Arrow (x, ty, acc)) xs acc) ps ty 
  in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let t =
    List.fold_right (fun (xs, _) acc -> 
      List.fold_right (fun x acc -> 
        Lambda (PVar x, acc)) xs acc) ps t
  in
  let* _ = kw "." in
  let* _ = set_user_state ctx in
  let* tp = top_parser () in
  return (Define (x, Ann (t, ty), tp))

and fixpoint_parser () =
  let* _ = kw "Fixpoint" in
  let* x = var_parser () in
  let* ctx = get_user_state in
  let* ps = many param_parser in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let ty =
    List.fold_right (fun (xs, ty) acc -> 
      List.fold_right (fun x acc -> 
        Arrow (x, ty, acc)) xs acc) ps ty 
  in
  let* _ = kw ":=" in
  let* t = t_parser () in
  let t =
    Fix (x,
      (List.fold_right (fun (xs, _) acc -> 
        List.fold_right (fun x acc ->
          Lambda (PVar x, acc)) xs acc) ps t))
  in
  let* _ = kw "." in
  let* _ = set_user_state ctx in
  let* tp = top_parser () in
  return (Define (x, Ann (t, ty), tp))

and datype_parser () =
  let* _ = kw "Inductive" in
  let* v_ctx, _ = get_user_state in
  let* id = id_parser ~intro:true ~tcons:true () in
  let* ps = many param_parser in
  let* _ = kw ":" in
  let* ts, n = tscope_parser () in
  let ts = 
    List.fold_right (fun (xs, t) ts -> 
      List.fold_right (fun x ts -> 
        PBind (x, t, ts)) xs ts) ps (PBase ts)
  in
  let id = Id.set_arity id (List.length ps + n) in
  let* _ = kw ":=" in
  let* cstr = many (constr_parser ps ()) in
  let* _ = kw "." in
  let* _, id_ctx = get_user_state in
  let* _ = set_user_state (v_ctx, id_ctx) in
  let* tp = top_parser () in
  return (Datype (TConstr (id, ts, cstr), tp))

and constr_parser ps () =
  let* _ = kw "|" in
  let* v_ctx, _ = get_user_state in
  let* id = id_parser ~intro:true () in
  let* _ = kw ":" in
  let* ts, n = tscope_parser () in
  let ts = 
    List.fold_right (fun (xs, t) ts -> 
      List.fold_right (fun x ts ->
        PBind (x, t, ts)) xs ts) ps (PBase ts)
  in
  let id = Id.set_arity id n in
  let* _, id_ctx = get_user_state in
  let* _ = set_user_state (v_ctx, id_ctx) in
  return (DConstr (id, ts))

and tscope_parser () =  
  let rec tscope_of_t t =
    match t with
    | Arrow (x, ty, t) ->
      let ts, n = tscope_of_t t in
      (TBind (x, ty, ts), n + 1)
    | _ -> (TBase t, 0)
  in
  let* t = t_parser () in
  return (tscope_of_t t)

and axiom_parser () =
  let* _ = kw "Axiom" in
  let* x = var_parser () in
  let id = Id.mk (Name.string_of x) () in
  let* _ = kw ":" in
  let* ty = t_parser () in
  let* _ = kw "." in
  let* tp = top_parser () in
  return (Define (x, Axiom (id, ty), tp))

and empty_parser () =
  return Empty

and top_parser () =
  choice [
    definition_parser ();
    fixpoint_parser ();
    datype_parser ();
    axiom_parser ();
    empty_parser ();
  ]

let parse s =
  let top, ctx = basic in
  match parse_string (ws () >> top_parser ()) s ctx with
  | Success t -> append_top top t
  | Failed (s, _) -> failwith s

let parse_ch ch =
  let top, ctx = basic in
  match parse_channel (ws () >> top_parser ()) ch ctx with
  | Success t -> append_top top t
  | Failed (s, _) -> failwith s
