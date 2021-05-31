open Bindlib
open Rig
open Terms
open Equality

module VarMap = Map.Make(
  struct
    type t = tvar
    let compare = compare_vars
  end)

type ctx = (term * rig) VarMap.t

let empty = VarMap.empty

let add x tq ctx = VarMap.add x tq ctx

let remove = VarMap.remove

let iter = VarMap.iter

let find x ctx =
  try VarMap.find x ctx
  with _ ->
    failwith ("Cannot find : " ^ name_of x)

let same ctx1 ctx2 =
  VarMap.equal
    (fun (t1, _) (t2, _) -> equal t1 t2)
    ctx1 ctx2

let scale n ctx =
  VarMap.map (fun (t, q) -> (t, q * n)) ctx

let sum ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 -> 
      match x1, x2 with
      | Some (t, q1), Some (_, q2) -> Some (t, q1 + q2)
      | _ -> None)
    ctx1 ctx2

let pp fmt ctx =
  Format.fprintf fmt "{\n";
  iter (fun x (t, q) -> 
    Format.fprintf fmt "\t%s :%a %a;\n" 
      (name_of x) Rig.pp q pp t)
    ctx;
  Format.fprintf fmt "}";