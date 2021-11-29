open Bindlib
open Names
open Terms
open Util
open Format

(* typing context *)
module VarMap = Map.Make (struct
  type t = Terms.t var

  let compare = compare_vars
end)

(* inductive definitions *)
module IdMap = Map.Make (Id)

type ctx = ty VarMap.t

type v_ctx = (ty * sort) VarMap.t

type id_ctx = ind IdMap.t

exception UnboundVarExn of Terms.t var

exception UnboundIdExn of Id.t

exception UnusedVarExn of Terms.t var

exception MergeDuplicationExn

let find_var x ctx =
  try VarMap.find x ctx with
  | _ -> raise (UnboundVarExn x)

let find_id id ctx =
  try IdMap.find id ctx with
  | _ -> raise (UnboundIdExn id)

let remove x ctx srt =
  match srt with
  | U -> ctx
  | L ->
    if VarMap.exists (fun y _ -> eq_vars x y) ctx then
      VarMap.remove x ctx
    else
      raise (UnusedVarExn x)

let equal ctx1 ctx2 = VarMap.equal (fun _ _ -> true) ctx1 ctx2

let merge ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 ->
      match (x1, x2) with
      | Some _, Some _ -> raise MergeDuplicationExn
      | Some _, None -> x1
      | None, Some _ -> x2
      | None, None -> None)
    ctx1 ctx2

let find_constr id ctx =
  let opt =
    IdMap.fold
      (fun _ ind acc ->
        match acc with
        | Some _ -> acc
        | None ->
          List.fold_left
            (fun acc constr ->
              match acc with
              | Some _ -> acc
              | None ->
                if Id.equal id constr.id then
                  Some constr
                else
                  None)
            None ind.cs)
      ctx None
  in
  match opt with
  | Some constr -> constr
  | None -> raise (UnboundIdExn id)

let pp fmt ctx =
  let pp_aux fmt ctx =
    VarMap.iter
      (fun x (t, srt) ->
        fprintf fmt "@[<v 0>@;<0 2>@[%a :%a@;<1 2>(%a)@]@]@?" pp_v x pp_s srt
          Terms.pp t)
      ctx
  in
  fprintf fmt "@[<hv>{@?@[%a@;<1 0>@]}@]@?" pp_aux ctx

let pp' fmt ctx =
  let pp_aux fmt ctx =
    VarMap.iter
      (fun x t ->
        fprintf fmt "@[<v 0>@;<0 2>@[%a :@;<1 2>(%a)@]@]@?" pp_v x Terms.pp t)
      ctx
  in
  fprintf fmt "@[<hv>{@?@[%a@;<1 0>@]}@]@?" pp_aux ctx