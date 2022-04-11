open Format
open MParser
open Name
open Raw
open Core
open Prelude
module SMap = Map.Make (String)
module SSet = Set.Make (String)

module ParseTerm = struct
  open RTerm

  let reserved =
    SSet.of_list
      [ "Main"
      ; "Definition"
      ; "Fixpoint"
      ; "Inductive"
      ; "Import"
      ; "Axiom"
      ; "U"
      ; "L"
      ; "forall"
      ; "linear"
      ; "fun"
      ; "fix"
      ; "let"
      ; "in"
      ; "match"
      ; "as"
      ; "return"
      ; "with"
      ; "end"
      ; "main"
      ; "proto"
      ; "channel"
      ; "fork"
      ; "send"
      ; "recv"
      ; "close"
      ; "stdin"
      ; "stdout"
      ; "stderr"
      ]

  type 'a parser = ('a, Var.t SMap.t * id_info SMap.t) MParser.t

  let ( let* ) = bind

  let rec repeatn p n =
    if n <= 0 then
      return []
    else
      let* x = p in
      let* xs = repeatn p (n - 1) in
      return (x :: xs)

  let rec comment () : unit parser =
    let any = any_char_or_nl >>$ () in
    let* _ = string "(*" in
    let* _ =
      many
        (let* opt =
           look_ahead (string "*)")
           >> return true
           <|> (comment () <|> any >> return false)
         in
         if opt then
           zero
         else
           return ())
    in
    let* _ = string "*)" in
    return ()

  let ws =
    many
      (choice
         [ blank >> return (); newline >> return (); comment () >> return () ])
    >>$ ()

  let kw s =
    let* _ = string s in
    let* _ = ws in
    return ()

  let parens p = kw "(" >> p << kw ")"

  let var_parser ?pat:(p = false) () =
    let* s1 = many1_chars (letter <|> char '_') in
    let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
    let* _ = ws in
    let s = s1 ^ s2 in
    if s = "_" then
      if p then
        return Var.__
      else
        zero
    else
      match SSet.find_opt s reserved with
      | Some _ -> fail (sprintf "not a valid varname(%s)" s)
      | None -> (
        let* vctx, ictx = get_user_state in
        match SMap.find_opt s vctx with
        | Some x -> return x
        | None ->
          let x = Var.mk s in
          let* _ = set_user_state (SMap.add s x vctx, ictx) in
          return x)

  let meta_parser () =
    let* _ = kw "_" in
    return (Meta.mk ())

  let id_parser ?intro:(p = false) ?is_ind:(t = false) ?arity:(n = 0) () =
    let* s1 = many1_chars (letter <|> char '_') in
    let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
    let* _ = ws in
    let s = s1 ^ s2 in
    if s = "_" then
      fail "non pattern id"
    else
      match SSet.find_opt s reserved with
      | Some _ -> (
        let* _, ictx = get_user_state in
        match SMap.find_opt s ictx with
        | Some id -> return id
        | None -> zero)
      | None -> (
        let* vctx, ictx = get_user_state in
        match SMap.find_opt s ictx with
        | Some id -> return id
        | None ->
          if p then
            let id_info = { id = Id.mk s; is_ind = t; arity = n } in
            let ictx = SMap.add s id_info ictx in
            let* _ = set_user_state (vctx, ictx) in
            return id_info
          else
            fail (sprintf "undefined id(%s)" s))

  let rec pvar_parser () =
    let* x = var_parser ~pat:true () in
    return (PVar x)

  and pcons_parser () =
    let* id_info = id_parser () in
    let n = id_info.arity in
    let is_ind = id_info.is_ind in
    let* ps = repeatn (p_parser ()) n in
    if is_ind then
      return (PInd (id_info.id, ps))
    else
      return (PConstr (id_info.id, ps))

  and p_tt_parser () = kw "(" >> kw ")" >>$ PConstr (Prelude.tt_id, [])

  and p_pair0_parser () =
    let* _ = kw "(" in
    let* p1 = p_parser () in
    let* _ = kw "," in
    let* p2 = p_parser () in
    let* _ = kw ")" in
    return (PConstr (Prelude.ex_intro_id, [ p1; p2 ]))

  and p_pair1_parser () =
    let* _ = kw "[" in
    let* p1 = p_parser () in
    let* _ = kw "," in
    let* p2 = p_parser () in
    let* _ = kw "]" in
    return (PConstr (Prelude.sig_intro_id, [ p1; p2 ]))

  and p_pair2_parser () =
    let* _ = kw "⟨" in
    let* p1 = p_parser () in
    let* _ = kw "," in
    let* p2 = p_parser () in
    let* _ = kw "⟩" in
    return (PConstr (Prelude.tnsr_intro_id, [ p1; p2 ]))

  and p0_parser () =
    let* _ = return () in
    choice
      (List.map attempt
         [ pcons_parser ()
         ; pvar_parser ()
         ; p_tt_parser ()
         ; p_pair0_parser ()
         ; p_pair1_parser ()
         ; p_pair2_parser ()
         ; parens (p_parser ())
         ])

  and p_parser () =
    let prod_parser =
      choice
        [ (kw "*" >>$ fun p1 p2 -> PInd (Prelude.ex_id, [ p1; p2 ]))
        ; (kw "^" >>$ fun p1 p2 -> PInd (Prelude.tnsr_id, [ p1; p2 ]))
        ]
    in
    chain_left1 (p0_parser ()) prod_parser

  let rec knd_parser () = kw "U" >>$ Knd U <|> (kw "L" >>$ Knd L)

  and forall_parser () =
    let* ctx = get_user_state in
    let* _ = kw "forall" in
    let* args =
      many
        (let* _ = kw "(" in
         let* xs = many1 (var_parser ()) in
         let* _ = kw ":" in
         let* a = t_parser () in
         let* _ = kw ")" in
         return (xs, a))
    in
    let* _ = kw "," in
    let* b = t_parser () in
    let m =
      List.fold_right
        (fun (xs, a) b -> List.fold_right (fun x b -> Pi (U, x, a, b)) xs b)
        args b
    in
    let* _ = set_user_state ctx in
    return m

  and linear_parser () =
    let* ctx = get_user_state in
    let* _ = kw "linear" in
    let* args =
      many
        (let* _ = kw "(" in
         let* xs = many1 (var_parser ()) in
         let* _ = kw ":" in
         let* a = t_parser () in
         let* _ = kw ")" in
         return (xs, a))
    in
    let* _ = kw "," in
    let* b = t_parser () in
    let m =
      List.fold_right
        (fun (xs, a) b -> List.fold_right (fun x b -> Pi (L, x, a, b)) xs b)
        args b
    in
    let* _ = set_user_state ctx in
    return m

  and fun_parser () =
    let* ctx = get_user_state in
    let* _ = kw "fun" in
    let* xs = many1 (p_parser ()) in
    let* _ = kw "=>" in
    let* b = t_parser () in
    let m = List.fold_right (fun x b -> Lam (U, x, b)) xs b in
    let* _ = set_user_state ctx in
    return m

  and lin_parser () =
    let* ctx = get_user_state in
    let* _ = kw "lin" in
    let* xs = many1 (p_parser ()) in
    let* _ = kw "=>" in
    let* b = t_parser () in
    let m = List.fold_right (fun x b -> Lam (L, x, b)) xs b in
    let* _ = set_user_state ctx in
    return m

  and fix_parser () =
    let* ctx = get_user_state in
    let* _ = kw "fix" in
    let* x = var_parser () in
    let* xs = many1 (p_parser ()) in
    let* _ = kw "=>" in
    let* b = t_parser () in
    let m = List.fold_right (fun x b -> Lam (U, x, b)) xs b in
    let* _ = set_user_state ctx in
    return (Fix (x, m))

  and let_parser () =
    let* ctx = get_user_state in
    let* _ = kw "let" in
    let* x = p_parser () in
    let* opt = option (attempt (kw ":" >> t_parser ())) in
    let* _ = kw ":=" in
    let* m = t_parser () in
    let m =
      match opt with
      | Some a -> Ann (m, a)
      | None -> m
    in
    let* _ = kw "in" in
    let* n = t_parser () in
    let* _ = set_user_state ctx in
    return (Let (x, m, n))

  and cons_parser () =
    let* id_info = id_parser () in
    let n = id_info.arity in
    let* ts = repeatn (t0_parser ()) n in
    if id_info.is_ind then
      return (Ind (id_info.id, ts))
    else
      return (Constr (id_info.id, ts))

  and match_parser () =
    let* _ = kw "match" in
    let* m = t_parser () in
    let* mot = mot_parser () in
    let* _ = kw "with" in
    let* cls = many (clause_parser ()) in
    let* _ = kw "end" in
    return (Match (m, mot, cls))

  and mot_parser () =
    choice
      (List.map attempt
         [ mot3_parser (); mot2_parser (); mot1_parser (); mot0_parser () ])

  and mot0_parser () = return Mot0

  and mot1_parser () =
    let* ctx = get_user_state in
    let* _ = kw "as" in
    let* x = var_parser () in
    let* _ = kw "return" in
    let* m = t_parser () in
    let* _ = set_user_state ctx in
    return (Mot1 (x, m))

  and mot2_parser () =
    let* ctx = get_user_state in
    let* _ = kw "in" in
    let* p = p_parser () in
    let* _ = kw "return" in
    let* m = t_parser () in
    let* _ = set_user_state ctx in
    return (Mot2 (p, m))

  and mot3_parser () =
    let* ctx = get_user_state in
    let* _ = kw "as" in
    let* x = var_parser () in
    let* _ = kw "in" in
    let* p = p_parser () in
    let* _ = kw "return" in
    let* m = t_parser () in
    let* _ = set_user_state ctx in
    return (Mot3 (x, p, m))

  and clause_parser () =
    let* ctx = get_user_state in
    let* _ = kw "|" in
    let* p = p_parser () in
    let* _ = kw "=>" in
    let* m = t_parser () in
    let* _ = set_user_state ctx in
    return (p, m)

  and tt_parser () = kw "(" >> kw ")" >>$ Constr (Prelude.tt_id, [])

  and pair0_parser () =
    let* _ = kw "(" in
    let* t1 = t_parser () in
    let* _ = kw "," in
    let* t2 = t_parser () in
    let* _ = kw ")" in
    return (Constr (Prelude.ex_intro_id, [ t1; t2 ]))

  and pair1_parser () =
    let* _ = kw "[" in
    let* t1 = t_parser () in
    let* _ = kw "," in
    let* t2 = t_parser () in
    let* _ = kw "]" in
    return (Constr (Prelude.sig_intro_id, [ t1; t2 ]))

  and pair2_parser () =
    let* _ = kw "⟨" in
    let* t1 = t_parser () in
    let* _ = kw "," in
    let* t2 = t_parser () in
    let* _ = kw "⟩" in
    return (Constr (Prelude.tnsr_intro_id, [ t1; t2 ]))

  and nat_parser () =
    let* s = many1_chars digit in
    let* _ = ws in
    match int_of_string_opt s with
    | Some n ->
      let rec loop i acc =
        if i < n then
          loop (i + 1) (Constr (Prelude.s_id, [ acc ]))
        else
          acc
      in
      return (loop 0 (Constr (Prelude.o_id, [])))
    | None -> fail "non-int"

  and ascii_parser () =
    let ascii n =
      let rec aux i n =
        let x = n mod 2 in
        let x =
          if x = 0 then
            Constr (Prelude.false_id, [])
          else
            Constr (Prelude.true_id, [])
        in
        let n = n / 2 in
        if i > 0 then
          x :: aux (i - 1) n
        else
          []
      in
      Constr (Prelude.ascii0_id, List.rev (aux 8 n))
    in
    let* c = any_char in
    if c = '\\' then
      choice
        [ char '\\' >>$ ascii (Char.code '\\')
        ; char '\"' >>$ ascii (Char.code '\"')
        ; char '\'' >>$ ascii (Char.code '\'')
        ; char 'n' >>$ ascii (Char.code '\n')
        ; char 't' >>$ ascii (Char.code '\t')
        ; char 'b' >>$ ascii (Char.code '\b')
        ; char 'r' >>$ ascii (Char.code '\r')
        ; char ' ' >>$ ascii (Char.code '\ ')
        ; (let* n1 = digit in
           let* n2 = digit in
           let* n3 = digit in
           let s = sprintf "0o%c%c%c" n1 n2 n3 in
           let n = int_of_string s in
           return (ascii n))
        ]
    else if c = '\"' || c = '\'' then
      zero
    else
      let n = Char.code c in
      return (ascii n)

  and char_parser () = char '\'' >> ascii_parser () << char '\'' << ws

  and asciix_parser () =
    let* ms = many (attempt (ascii_parser ())) in
    let m =
      List.fold_right
        (fun m acc -> Constr (Prelude.string0_id, [ m; acc ]))
        ms
        (Constr (Prelude.emptyString_id, []))
    in
    return m

  and string_parser () = char '\"' >> asciix_parser () << char '\"' << ws

  and main_parser () = kw "main" >> return Main

  and proto_parser () = kw "proto" >> return Proto

  and end_parser () = kw "$" >> return End

  and inp_parser () =
    let* ctx = get_user_state in
    let* _ = kw "?" in
    let* args =
      many1
        (attempt
           (let* _ = kw "(" in
            let* xs = many1 (var_parser ()) in
            let* _ = kw ":" in
            let* a = t_parser () in
            let* _ = kw ")" in
            return (xs, a)))
      <|> let* a = t_parser () in
          return [ ([ Var.__ ], a) ]
    in
    let* _ = kw "," in
    let* b = t_parser () in
    let m =
      List.fold_right
        (fun (xs, a) b -> List.fold_right (fun x b -> Inp (x, a, b)) xs b)
        args b
    in
    let* _ = set_user_state ctx in
    return m

  and out_parser () =
    let* ctx = get_user_state in
    let* _ = kw "!" in
    let* args =
      many1
        (attempt
           (let* _ = kw "(" in
            let* xs = many1 (var_parser ()) in
            let* _ = kw ":" in
            let* a = t_parser () in
            let* _ = kw ")" in
            return (xs, a)))
      <|> let* a = t_parser () in
          return [ ([ Var.__ ], a) ]
    in
    let* _ = kw "," in
    let* b = t_parser () in
    let m =
      List.fold_right
        (fun (xs, a) b -> List.fold_right (fun x b -> Out (x, a, b)) xs b)
        args b
    in
    let* _ = set_user_state ctx in
    return m

  and ch_parser () =
    let* _ = kw "channel" in
    let* m = t_parser () in
    return (Ch m)

  and fork_parser () =
    let* ctx = get_user_state in
    let* _ = kw "fork" in
    let* _ = kw "(" in
    let* x = var_parser () in
    let* _ = kw ":" in
    let* a = t_parser () in
    let* _ = kw ")" in
    let* _ = kw ":=" in
    let* m = t_parser () in
    let* _ = kw "in" in
    let* n = t_parser () in
    let* _ = set_user_state ctx in
    return (Fork (x, a, m, n))

  and send_parser () =
    let* _ = kw "send" in
    let* m = t0_parser () in
    return (Send m)

  and recv_parser () =
    let* _ = kw "recv" in
    let* m = t0_parser () in
    return (Recv m)

  and close_parser () =
    let* _ = kw "close" in
    let* m = t0_parser () in
    return (Close m)

  and t0_parser () =
    let* _ = return () in
    choice
      (List.map attempt
         [ cons_parser ()
         ; (var_parser () >>= fun x -> return (Var x))
         ; (meta_parser () >>= fun x -> return (Meta x))
         ; knd_parser ()
         ; forall_parser ()
         ; linear_parser ()
         ; fun_parser ()
         ; lin_parser ()
         ; let_parser ()
         ; match_parser ()
         ; tt_parser ()
         ; pair0_parser ()
         ; pair1_parser ()
         ; pair2_parser ()
         ; nat_parser ()
         ; char_parser ()
         ; string_parser ()
         ; main_parser ()
         ; proto_parser ()
         ; end_parser ()
         ; inp_parser ()
         ; out_parser ()
         ; ch_parser ()
         ; fork_parser ()
         ; send_parser ()
         ; recv_parser ()
         ; close_parser ()
         ; parens (t_parser ())
         ])

  and t1_parser () =
    let* _ = return () in
    let* h = t0_parser () in
    let* sp = many (t0_parser ()) in
    let m = List.fold_left (fun h n -> App (h, n)) h sp in
    return m

  and t2_parser () =
    let arrow_parser () =
      let* _ = kw "->" in
      return (fun a b -> Pi (U, Var.__, a, b))
    in
    let lolli_parser () =
      let* _ = kw "-o" in
      return (fun a b -> Pi (L, Var.__, a, b))
    in
    chain_right1 (t1_parser ()) (arrow_parser () <|> lolli_parser ())

  and t_parser () =
    attempt (t2_parser ())
    <|> let* _ = kw "(" in
        let* m = t2_parser () in
        let* _ = kw ":" in
        let* a = t2_parser () in
        let* _ = kw ")" in
        return (Ann (m, a))
end

module ParseTop = struct
  open ParseTerm
  open RTerm
  open RTop

  exception ParseError of string

  let param_parser =
    let* _ = kw "(" in
    let* xs = many1 (var_parser ~pat:true ()) in
    let* _ = kw ":" in
    let* a = t_parser () in
    let* _ = kw ")" in
    return (xs, a)

  let rec definition_parser () =
    let* _ = kw "Definition" in
    let* x = var_parser ~pat:true () in
    let* ctx = get_user_state in
    let* ps = many param_parser in
    let* _ = kw ":" in
    let* a = t_parser () in
    let a =
      List.fold_right
        (fun (xs, a) acc ->
          List.fold_right (fun x acc -> Pi (U, x, a, acc)) xs acc)
        ps a
    in
    let* _ = kw ":=" in
    let* m = t_parser () in
    let m =
      List.fold_right
        (fun (xs, _) acc ->
          List.fold_right (fun x acc -> Lam (U, PVar x, acc)) xs acc)
        ps m
    in
    let* _ = kw "." in
    let* _ = set_user_state ctx in
    let* tp = tp_parser () in
    return (Define (x, Ann (m, a), tp))

  and fixpoint_parser () =
    let* _ = kw "Fixpoint" in
    let* x = var_parser () in
    let* ctx = get_user_state in
    let* ps = many param_parser in
    let* _ = kw ":" in
    let* a = t_parser () in
    let a =
      List.fold_right
        (fun (xs, a) acc ->
          List.fold_right (fun x acc -> Pi (U, x, a, acc)) xs acc)
        ps a
    in
    let* _ = kw ":=" in
    let* m = t_parser () in
    let m =
      Fix
        ( x
        , List.fold_right
            (fun (xs, _) acc ->
              List.fold_right (fun x acc -> Lam (U, PVar x, acc)) xs acc)
            ps m )
    in
    let* _ = kw "." in
    let* _ = set_user_state ctx in
    let* tp = tp_parser () in
    return (Define (x, Ann (m, a), tp))

  and induct_parser () =
    let* _ = kw "Inductive" in
    let* vctx, ictx = get_user_state in
    let* id_info = id_parser ~intro:true ~is_ind:true () in
    let* ps = many param_parser in
    let* _ = kw ":" in
    let* ts, n = tscope_parser () in
    let a =
      List.fold_right
        (fun (xs, a) acc ->
          List.fold_right (fun x acc -> PBind (x, a, acc)) xs acc)
        ps (PBase ts)
    in
    let id_info = { id_info with arity = List.length ps + n } in
    let ictx = SMap.add (Id.string_of id_info.id) id_info ictx in
    let* _ = update_user_state (fun (vctx, _) -> (vctx, ictx)) in
    let* _ = kw ":=" in
    let* cs = many (constr_parser ps ()) in
    let* _ = kw "." in
    let* _ = update_user_state (fun (_, ictx) -> (vctx, ictx)) in
    let* tp = tp_parser () in
    return (Induct (Ind (id_info.id, a, cs), tp))

  and constr_parser ps () =
    let* _ = kw "|" in
    let* vctx, ictx = get_user_state in
    let* id_info = id_parser ~intro:true () in
    let* _ = kw ":" in
    let* ts, n = tscope_parser () in
    let a =
      List.fold_right
        (fun (xs, a) acc ->
          List.fold_right (fun x acc -> PBind (x, a, acc)) xs acc)
        ps (PBase ts)
    in
    let id_info = { id_info with arity = n } in
    let ictx = SMap.add (Id.string_of id_info.id) id_info ictx in
    let* _ = set_user_state (vctx, ictx) in
    return (Constr (id_info.id, a))

  and tscope_parser () =
    let rec tscope_of_t m =
      match m with
      | Pi (U, x, a, b) ->
        let ts, n = tscope_of_t b in
        (TBind (x, a, ts), n + 1)
      | _ -> (TBase m, 0)
    in
    let* t = t_parser () in
    return (tscope_of_t t)

  and import_parser () =
    let* _ = kw "Import" in
    let* id_info = id_parser () in
    let* m = t_parser () in
    let* _ = kw "as" in
    let* x = var_parser () in
    let* _ = kw "." in
    let* tp = tp_parser () in
    return (Import (id_info.id, m, x, tp))

  and axiom_parser () =
    let* _ = kw "Axiom" in
    let* x = var_parser () in
    let id = Id.mk (Var.string_of x) in
    let* _ = kw ":" in
    let* a = t_parser () in
    let* _ = kw "." in
    let* tp = tp_parser () in
    return (Define (x, Axiom (id, a), tp))

  and main_parser () =
    let* _ = kw "Definition" in
    let* _ = kw "Main" in
    let* _ = kw ":=" in
    let* m = t_parser () in
    let* _ = kw "." in
    let* ctx = get_user_state in
    return (Main m)

  and tp_parser () =
    choice
      (List.map attempt
         [ definition_parser ()
         ; fixpoint_parser ()
         ; induct_parser ()
         ; import_parser ()
         ; axiom_parser ()
         ; main_parser ()
         ])

  let parse_ch ch =
    let ctx = Prelude.(vctx, ictx) in
    match parse_channel (ws >> tp_parser ()) ch ctx with
    | Success t -> append_t Prelude.raw t
    | Failed (s, _) -> raise (ParseError s)
end
