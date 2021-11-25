open Names
open Constr
open Context
open Equality

let rec check ctx ty q t =
  let _ = Format.printf "ty: %a\nq: %d\nt: %a\n\n" pp ty q pp t in
  match t with
  | Rel _ -> failwith "Rel"
  | Var id ->
    let t = find id ctx in
    let _ = assert (equal t.elem ty) in
    let _ = assert (t.q >= q) in
    add id { t with q = t.q - q } ctx
  | Type ->
    let _ = assert (equal Type ty) in
    ctx
  | Prod (bind, t) ->
    (* target type *)
    let _ = assert (equal Type ty) in
    let _ = assert (q = 0) in
    (* domain type *)
    let ctx0 = scale 0 ctx in
    let bind, t = unbind bind t in
    let bind_rec = rec_of_binder bind in
    let _ = is_type ctx0 bind_rec.annot in
    (* co-domain type *)
    let ctx1 =
      match bind_rec.binder with
      | Anonymous -> ctx0
      | Name id ->
        let elem = { elem = bind_rec.annot; q = 0 } in
        add id elem ctx0
    in
    let _ = is_type ctx1 t in
    ctx
  | Lambda (bind1, t) -> (
    (* target type *)
    let ctx0 = scale 0 ctx in
    let _ = is_type ctx0 ty in
    match whnf ty with
    | Prod (bind2, ty) -> (
      let bind1, t, ty = unbind2 bind1 t ty in
      let bind1_rec = rec_of_binder bind1 in
      let bind2_rec = rec_of_binder bind2 in
      (* annotation types *)
      let _ = assert (equal bind1_rec.annot bind2_rec.annot) in
      let _ = assert (bind1_rec.q = bind2_rec.q) in
      (* body type *)
      match bind1_rec.binder with
      | Anonymous ->
        let _ = assert (bind1_rec.q = 0) in
        check ctx ty q t
      | Name id ->
        let elem = { elem = bind2_rec.annot; q = q * bind2_rec.q } in
        let ctx = add id elem ctx in
        let ctx = check ctx ty q t in
        let t = find id ctx in
        let _ = assert (t.q = 0) in
        remove id ctx)
    | _ -> failwith "Lambda")
  | Fix (bind, t) -> (
    (* target type *)
    let ctx0 = scale 0 ctx in
    let _ = is_type ctx0 ty in
    (* annotation type *)
    let bind, t = unbind bind t in
    let bind_rec = rec_of_binder bind in
    let _ = is_type ctx0 bind_rec.annot in
    (* body type *)
    match bind_rec.binder with
    | Anonymous -> failwith "Fix1"
    | Name id ->
      let elem = { elem = bind_rec.annot; q = q * bind_rec.q } in
      let ctx = add id elem ctx in
      let ctx = check ctx ty q t in
      let t = find id ctx in
      let _ = assert (t.q = 0) in
      remove id ctx)
  | App (t1, t2) -> (
    let ctx1, ty1 = infer ctx q t1 in
    match whnf ty1 with
    | Prod (bind, ty1) ->
      let bind, ty1 = unbind bind ty1 in
      let bind_rec = rec_of_binder bind in
      let q = if q = 0 || bind_rec.q = 0 then 0 else 1 in
      let ctx2 = check ctx bind_rec.annot q t2 in
      let ctx3 = sum ctx1 (scale bind_rec.q ctx2) in
      let ctx4 = sum ctx3 (scale (-bind_rec.q) ctx) in
      let _ = assert (is_positive ctx4) in
      let ty1 = subst bind ty1 t2 in
      let _ = assert (equal ty1 ty) in
      ctx4
    | _ -> failwith "App")
  | Magic -> ctx

and infer ctx q = function
  | Rel _ -> failwith "Rel"
  | Var id ->
    let t = find id ctx in
    let _ = assert (t.q >= q) in
    (add id { t with q = t.q - q } ctx, t.elem)
  | Type -> (ctx, Type)
  | Prod (bind, t) ->
    let ctx = check ctx Type q (Prod (bind, t)) in
    (ctx, Type)
  | Lambda (b, t) ->
    let b, t = unbind b t in
    let b_rec = rec_of_binder b in
    let ctx = check ctx Type q b_rec.annot in
    let ctx =
      match b_rec.binder with
      | Anonymous ->
        let _ = assert (b_rec.q = 0) in
        ctx
      | Name id ->
        let elem = { elem = b_rec.annot; q = q * b_rec.q } in
        add id elem ctx
    in
    let ctx, ty = infer ctx q t in
    let b, ty = bind b_rec ty in
    (ctx, Prod (b, ty))
  | Fix (b, t) ->
    let b, t = unbind b t in
    let bind_rec = rec_of_binder b in
    let ctx = check ctx Type q bind_rec.annot in
    let ctx =
      match bind_rec.binder with
      | Anonymous -> failwith "Fix"
      | Name id ->
        let elem = { elem = bind_rec.annot; q = q * bind_rec.q } in
        add id elem ctx
    in
    infer ctx q t
  | App (t1, t2) -> (
    let ctx1, ty1 = infer ctx q t1 in
    match whnf ty1 with
    | Prod (bind, ty1) ->
      let bind, ty1 = unbind bind ty1 in
      let bind_rec = rec_of_binder bind in
      let q' = if q = 0 || bind_rec.q = 0 then 0 else 1 in
      let ctx2 = check ctx bind_rec.annot q' t2 in
      let _ = assert (Context.equal ctx1 ctx2) in
      let ctx' = sum ctx1 (scale bind_rec.q ctx2) in
      let ctx' = sum ctx' (scale (-bind_rec.q) ctx) in
      let _ = assert (is_positive ctx') in
      let ty1 = subst bind ty1 t2 in
      (ctx', ty1)
    | _ -> failwith "App")
  | _ -> failwith ""

and is_type ctx t =
  let ctx = check ctx Type 0 t in
  assert (is_zero ctx)
