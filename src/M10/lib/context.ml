open Bindlib
open Util
open Format
open Names
open Terms

module VarMap = Map.Make(
  struct
    type t = Terms.t var
    let compare = compare_vars
  end)

module IdMap = Map.Make(Id)

type v_ctx = (t * sort) VarMap.t
type id_ctx = tcons IdMap.t

let find x ctx =
  try VarMap.find x ctx
  with _ -> failwith (asprintf "cannot find: %a" pp_v x)

let remove x ctx srt =
  match srt with
  | Type -> ctx
  | Linear ->
    if VarMap.exists (fun y _ -> eq_vars x y) ctx
    then VarMap.remove x ctx
    else failwith ("unused variable:" ^ name_of x)

let equal ctx1 ctx2 = 
  VarMap.equal (fun _ _ -> true) ctx1 ctx2

let merge ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 ->
      match x1, x2 with 
      | Some _, Some _ -> failwith "merge duplication"
      | Some _, None -> x1
      | None, Some _ -> x2
      | None, None -> None)
    ctx1 ctx2

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
    VarMap.iter (fun x (t, srt) -> 
      fprintf fmt "@[<v 0>@;<0 2>@[%a :%a@;<1 2>(%a)@]@]@?" 
        pp_v x pp_s srt Terms.pp t) ctx
  in
  fprintf fmt "@[<hv>{@?@[%a@;<1 0>@]}@]@?" pp_aux ctx

let pp' fmt ctx =
  let pp_aux fmt ctx =
    VarMap.iter (fun x t -> 
      fprintf fmt "@[<v 0>@;<0 2>@[%a :@;<1 2>(%a)@]@]@?" 
        pp_v x Terms.pp t) ctx
  in
  fprintf fmt "@[<hv>{@?@[%a@;<1 0>@]}@]@?" pp_aux ctx