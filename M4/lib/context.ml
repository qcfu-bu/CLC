open Bindlib
open Terms
open Equality

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
let merge ctx1 ctx2 = 
  VarMap.merge
    (fun _ x1 x2 ->
      match x1, x2 with 
      | Some _, _ -> x1
      | _, Some _ -> x2
      | _ -> None)
    ctx1 ctx2
let is_empty = VarMap.is_empty