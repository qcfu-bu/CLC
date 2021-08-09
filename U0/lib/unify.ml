open Bindlib
open Terms
open Tcheck

let rec spine t =
  match t with
  | App (t1, t2) ->
    let (h, ts) = spine t1 in
    (h, ts @ [t2])
  | _ -> (t, [])

let rec unwind ty =
  match ty with
  | Const _ -> ([], ty)
  | Fun (ty1, ty2) ->
    let tys, ty = unwind ty2 in
    (ty1 :: tys, ty)

let rec unbind_all t =
  match t with
  | Lambda (ty, b) ->
    let x, t = unbind b in
    let xs, t = unbind_all t in
    ((x, ty) :: xs, t)
  | _ -> ([], t)

let rec unbind2_all t1 t2 =
  match t1, t2 with
  | Lambda (ty1, b1), Lambda (ty2, b2) ->
    let x, t1, t2 = unbind2 b1 b2 in
    let xs1, xs2, t1, t2 = unbind2_all t1 t2 in
    ((x, ty1) :: xs1, (x, ty2) :: xs2, t1, t2)
  | _ -> ([], [], t1, t2)

let rec bind_all xs t =
  match xs with
  | (x, ty) :: xs ->
    let b = unbox (bind_var x (lift t)) in
    bind_all xs (Lambda (ty, b))
  | [] -> t

let is_rigid t =
  let _, t = unbind_all t in
  let h, _ = spine t in
  match h with
  | V _ -> true
  | C _ -> true
  | _ -> false

let simpl ps =
  let rec simpl_aux ps = 
    match ps with
    | (t1, t2) :: ps -> (
      if te_eq t1 t2 
      then simpl_aux ps
      else
        let xs1, xs2, b1, b2 = unbind2_all t1 t2 in
        let h1, ts1 = spine b1 in
        let h2, ts2 = spine b2 in
        match h1, h2 with
        | V x1, V x2 -> 
          if eq_vars x1 x2 
          then
            let ps' = 
              List.map2 
                (fun t1 t2 -> (bind_all xs1 t1, bind_all xs2 t2)) 
                ts1 ts2
            in
            simpl_aux (ps' @ ps)
          else assert false
        | _, M _ -> (t2, t1) :: simpl_aux ps
        | C c1, C c2 -> 
          if C.eq c1 c2 
          then
            let ps' = 
              List.map2 
                (fun t1 t2 -> (bind_all xs1 t1, bind_all xs2 t2)) 
                ts1 ts2
            in
            simpl_aux (ps' @ ps)
          else assert false
        | _ -> (t1, t2) :: simpl_aux ps)
    | [] -> []
  in 
  let ps = simpl_aux ps in
  if List.exists (fun (_, t) -> is_rigid t) ps
  then (Some ps)
  else None


let rec imitation vctx ps =
  match ps with
  | (t1, t2) :: ps -> (
    if te_eq t1 t2 
    then imitation vctx ps
    else
      let xs1, xs2, b1, b2 = unbind2_all t1 t2 in
      let h1, ts1 = spine b1 in
      let h2, ts2 = spine b2 in
      match h1, h2 with
      | M x, C _ ->
        let vctx1 = xs1 @ vctx in
        let zs = List.map
          (fun t -> 
            let ty = infer vctx1 t in
            let z = mk "z" in
            (z, ty)) ts1 
        in
        let vs = List.map (fun (x, _) -> _V x) zs in
        let tys = List.map (fun (_, ty) -> ty) zs in
        let vctx2 = xs2 @ vctx in
        let ts = List.map
          (fun t -> 
            let ty = fun' tys (infer vctx2 t) in
            let h = M.mk "H" ty in
            _App' (_M h) vs) ts2
        in
        let t = _App' (lift h2) ts in
        (x, unbox (_Lambda' zs t)) :: imitation vctx ps
      | _ -> imitation vctx ps)
  | _ -> []

let rec projection vctx ps =
  match ps with
  | (t1, t2) :: ps -> (
    if te_eq t1 t2
    then projection vctx ps
    else
      let xs1, _, b1, b2 = unbind2_all t1 t2 in
      let h1, ts1 = spine b1 in
      let h2, _ = spine b2 in
      match h1, h2 with
      | M x, C _ | M x, V _ ->
        let ty = M.ty x in
        let _, ty = unwind ty in
        let vctx1 = xs1 @ vctx in
        let zs = List.map
          (fun t -> 
            let ty = infer vctx1 t in
            let z = mk "z" in
            (z, ty)) ts1
        in
        let zs' = List.fold_right 
          (fun (z, ty') acc -> 
            let _, ty' = unwind ty' in
            if ty_eq ty ty'
            then (z, ty) :: acc 
            else acc) zs []
        in
        let z_vs = List.map (fun (x, _) -> _V x) zs in
        let z_tys = List.map (fun (_, ty) -> ty) zs in
        let ss = List.map 
          (fun (z, ty) ->
            let tys, _ = unwind ty in
            let ts = List.map
              (fun ty -> 
                let h = M.mk "H" (fun' z_tys ty) in
                _App' (_M h) z_vs) tys
            in
            let t = _App' (_V z) ts in
            (x, unbox (_Lambda' zs t))) zs'
        in
        ss @ projection vctx ps
      | _ -> projection vctx ps)
  | _ -> []

let unify vctx ps =
  let rec unify_aux ps =
    match simpl ps with
    | Some ps -> (
      let _ = Format.printf "@[ps1 :=@;%a@]@." Util.pp_ps ps in
      let ss1 = imitation vctx ps in
      let ss2 = projection vctx ps in
      let ss = ss1 @ ss2 in
      if (ss = []) 
      then failwith "Error."
      else
        let pss = 
          List.map (fun (x, t) ->
          List.map (fun (t1, t2) -> 
            (nf (msubst t1 x t), nf (msubst t2 x t))) ps) ss
        in
        let ps = List.concat pss in
        let _ = Format.printf "@[ps2 :=@;%a@]@." Util.pp_ps ps in
        unify_aux ps)
    | None -> Format.printf "Done.@."
  in
  unify_aux ps