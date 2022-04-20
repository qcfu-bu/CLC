open Format
open Bindlib
open Name
open Core
open Term
open Top

let find_v x ctx =
  try VMap.find x ctx with
  | _ -> failwith (asprintf "unbound variable(%a)" pp_v x)

let find_id id ctx =
  try IMap.find id ctx with
  | _ -> failwith (asprintf "unbound ind id(%a)" Id.pp id)

let find_idc id ctx =
  let opt =
    IMap.fold
      (fun _ (Ind (_, _, cs)) acc ->
        match acc with
        | Some _ -> acc
        | None ->
          List.fold_left
            (fun acc (Constr (idc, ps)) ->
              match acc with
              | Some _ -> acc
              | None ->
                if Id.equal id idc then
                  Some (Constr (idc, ps))
                else
                  None)
            None cs)
      ctx None
  in
  match opt with
  | Some c -> c
  | None -> failwith (asprintf "unbound constr id(%a)" Id.pp id)

let equal ctx1 ctx2 = VMap.equal (fun _ _ -> true) ctx1 ctx2

let remove x ctx s =
  match s with
  | U -> ctx
  | L ->
    if VMap.exists (fun y _ -> eq_vars x y) ctx then
      VMap.remove x ctx
    else
      failwith (asprintf "unused variable(%a)" pp_v x)

let merge ctx1 ctx2 =
  VMap.merge
    (fun _ x1 x2 ->
      match (x1, x2) with
      | Some _, Some _ -> failwith "merge duplication"
      | Some _, None -> x1
      | None, Some _ -> x2
      | None, None -> None)
    ctx1 ctx2
