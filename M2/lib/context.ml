open Bindlib
open Ring
open Terms
open Equality

module VarMap = Map.Make(
  struct
    type t = tvar
    let compare = Bindlib.compare_vars
  end)

type ctx = (term * ring) VarMap.t

let empty = VarMap.empty

let add v t q ctx = VarMap.add v (t, q) ctx

let remove = VarMap.remove

let iter = VarMap.iter

let find v ctx =
  try VarMap.find v ctx
  with _ -> 
    failwith ("Cannot find " ^ name_of v ^ " in context")

let contract x ctx =
  let q = snd (find x ctx) in
  if q = z || q = w
  then remove x ctx
  else failwith ("Cannot contract linear " ^ name_of x)

let equal ctx1 ctx2 =
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
      | Some _, _ -> x1
      | _, Some _ -> x2
      | _ -> None)
    ctx1 ctx2

let sub ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 ->
      match x1, x2 with 
      | Some (t, q1), Some (_, q2) -> Some (t, q1 - q2)
      | _ -> None)
    ctx1 ctx2

let is_positive ctx =
  VarMap.for_all (fun _ (_, q) -> z <= q) ctx

let is_zero ctx =
  VarMap.for_all (fun _ (_, q) -> q = z) ctx
