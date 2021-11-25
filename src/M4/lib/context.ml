open Bindlib
open Terms

module VarMap = Map.Make(
  struct
    type t = tvar
    let compare = compare_vars
  end)

type ctx = ty VarMap.t

let empty = VarMap.empty
let add = VarMap.add
let find x = 
  try VarMap.find x 
  with _ -> failwith ("cannot find " ^ (name_of x))
let contains x = VarMap.exists (fun y _ -> eq_vars x y)
let remove = VarMap.remove
let equal ctx1 ctx2 = 
  VarMap.equal (fun _ _ -> true) ctx1 ctx2
let intersect ctx1 ctx2 = 
  VarMap.merge
    (fun _ x1 x2 ->
      match x1, x2 with 
      | Some _, Some _ -> x1
      | _ -> None)
    ctx1 ctx2
let is_empty = VarMap.is_empty
let not_in x = 
  VarMap.for_all
    (fun y _ -> not (eq_vars x y))
let is_subset ctx1 ctx2 =
  VarMap.for_all (fun x _ -> 
    VarMap.exists (fun y _ -> 
      eq_vars x y) ctx2) ctx1

let pp_ctx fmt ctx = 
  Format.fprintf fmt "{@?";
  VarMap.iter
    (fun x ty -> 
      Format.fprintf fmt "@[<v 0>@;<0 2>@[%s :@;<1 2>%a@]@]@?"
        (name_of x) pp ty) ctx;
  Format.fprintf fmt "\n}@?"