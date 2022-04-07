  let rec aeq m1 m2 =
    match (m1, m2) with
    | Meta x1, Meta x2 -> Meta.equal x1 x2
    | Ann (m1, a1), Ann (m2, a2) -> aeq m1 m2 && aeq a1 a2
    | Knd s1, Knd s2 -> s1 = s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Pi (a1, b1, s1), Pi (a2, b2, s2) ->
      aeq a1 a2 && eq_binder aeq b1 b2 && s1 = s2
    | Lam (m1, s1), Lam (m2, s2) -> eq_binder aeq m1 m2 && s1 = s2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (m1, n1), Let (m2, n2) -> aeq m1 m2 && eq_binder aeq n1 n2
    | Ind (id1, ms1), Ind (id2, ms2) ->
      Id.equal id1 id2 && List.equal aeq ms1 ms2
    | Constr (id1, ms1), Constr (id2, ms2) ->
      Id.equal id1 id2 && List.equal aeq ms1 ms2
    | Match (m1, mot1, cls1), Match (m2, mot2, cls2) ->
