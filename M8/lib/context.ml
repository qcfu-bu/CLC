open Bindlib
open Format
open Names
open Terms
open Equality

module VarMap = Map.Make(
  struct
    type t = Terms.t var
    let compare = compare_vars
  end)

module IdMap = Map.Make(Id)

type m = Ty | Ln

let ( <= ) m1 m2 =
  match m1, m2 with
  | Ty, Ty -> true
  | Ty, Ln -> false
  | Ln, Ty -> true
  | Ln, Ln -> true

let min m1 m2 = 
  if m1 <= m2 
  then m1
  else m2

let empty = VarMap.empty

let singleton = VarMap.singleton

let add = VarMap.add

let is_empty = VarMap.is_empty

let find x ctx = 
  try VarMap.find x ctx
  with _ -> failwith ("cannot find : " ^ name_of x)

let remove x ctx m =
  match m with
  | Ty -> ctx
  | Ln ->
    let _ = find x ctx in
    VarMap.remove x ctx

let pure ctx =
  VarMap.filter 
    (fun _ (_, m) -> 
      match m with
      | Ln -> false
      | Ty -> true) 
    ctx

let equal ctx1 ctx2 =
  VarMap.equal (fun ty1 ty2 -> equal ty1 ty2) ctx1 ctx2

let merge ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 ->
      match x1, x2 with  
      | Some _, Some _ -> failwith "merge"
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
  let pp_aux fmt =
    VarMap.iter (fun x (t, m) -> 
      match m with
      | Ty ->
        fprintf fmt "@[<v 0>@;<0 2>@[%s : @;<1 2>(%a)@]@]@?" 
          (name_of x) pp t
      | Ln ->
        fprintf fmt "@[<v 0>@;<0 2>@[%s ::@;<1 2>(%a)@]@]@?" 
          (name_of x) pp t)
  in
  fprintf fmt "@[<hv>{@?@[%a@;<1 0>@]}@]@?" pp_aux ctx