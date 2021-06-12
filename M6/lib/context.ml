open Bindlib
open Rig
open Terms
open Format

module VarMap = Map.Make(
  struct
    type t = tvar
    let compare = compare_vars
  end)

type ctx = (t * rig * rig) VarMap.t

let empty = VarMap.empty

let add x tq ctx = VarMap.add x tq ctx

let remove = VarMap.remove

let iter = VarMap.iter

let find x ctx =
  try VarMap.find x ctx
  with _ ->
    failwith ("Cannot find : " ^ name_of x)

let occur x ctx =
  try 
    let _, r, _ = VarMap.find x ctx in r
  with _ -> Rig.Zero

let same ctx1 ctx2 =
  VarMap.equal
    (fun (_, r11, r12) (_, r21, r22) -> r11 = r21 && r12 = r22)
    ctx1 ctx2

let scale n ctx =
  VarMap.map (fun (t, q1, q2) -> (t, q1 * n, q2)) ctx

let sum ctx1 ctx2 =
  VarMap.merge
    (fun _ x1 x2 -> 
      match x1, x2 with
      | Some (t, q1, q), Some (_, q2, _) -> Some (t, q1 + q2, q)
      | Some _, None -> x1
      | None, Some _ -> x2
      | None, None -> None)
    ctx1 ctx2

let pure ctx = VarMap.filter (fun _ (_, _, r) -> r = W) ctx

let pp fmt ctx =
  fprintf fmt "{@?";
  iter (fun x (t, q1, q2) -> 
    fprintf fmt "@[<v 0>@;<0 2>@[%s :%a@;<1 2>(%a)::%a@]@]@?" 
      (name_of x) Rig.pp q1 pp t Rig.pp q2)
    ctx;
  fprintf fmt "\n}@?";

