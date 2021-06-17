open Bindlib
open Format
open Rig
open Names
open Terms

module VarMap = Map.Make(
  struct
    type t = Terms.t var
    let compare = compare_vars
  end)

module IdMap = Map.Make(Id)

type v_ctx = (t * rig * rig) VarMap.t
type id_ctx = tcons VarMap.t

let find x ctx =
  try VarMap.find x ctx
  with _ -> failwith ("cannot find : " ^ name_of x)

let occur x ctx =
  try let _, r, _ = VarMap.find x ctx in r
  with _ -> Rig.Zero

let equal ctx1 ctx2 =
  VarMap.equal
    (fun (_, r1, m1) (_, r2, m2) -> 
      m1 = m2 && if m1 = One then r1 = r2 else true) 
    ctx1 ctx2
  
let scale r ctx =
  VarMap.map (fun (t, r', m) -> (t, r * r', m)) ctx

let merge ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 -> 
      match x1, x2 with 
      | Some (t, r1, m), Some (_, r2, _) -> Some (t, r1 + r2, m)
      | Some _, None -> x1
      | None, Some _ -> x2
      | None, None -> None)
    ctx1 ctx2

let pure ctx = 
  VarMap.filter (fun _ (_, _, m) -> m = W) ctx

let is_pure ctx =
  VarMap.for_all 
    (fun _ (_, r, m) ->
      if m = One
      then r = Zero
      else true)
    ctx

let find_dcons id ctx =
  let opt =
    IdMap.fold 
      (fun _ (TConstr (_, _, ds)) acc -> 
        match acc with
        | Some _ -> acc
        | _ ->
          List.fold_left
            (fun acc (DConstr (id', _) as d) -> 
              match acc with 
              | Some _ -> acc
              | _ ->
                if Id.equal id id'
                then Some d
                else None)
            None ds)
      ctx None
    in 
    match opt with
    | Some d -> d
    | None -> failwith (asprintf "find_dcons(%a)" Id.pp id)

let pp fmt ctx =
  let pp_aux fmt ctx =
    VarMap.iter (fun x (t, q1, q2) -> 
      fprintf fmt "@[<v 0>@;<0 2>@[%s :%a@;<1 2>(%a)::%a@]@]@?" 
        (name_of x) Rig.pp q1 pp t Rig.pp q2) ctx
  in
  fprintf fmt "@[<hv>{@?@[%a@;<1 0>@]}@]@?" pp_aux ctx