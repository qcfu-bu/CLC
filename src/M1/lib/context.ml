open Names
module FMap = Map.Make (Id)

type 'a elem_q = { elem : 'a; q : int }

type 'a t = 'a elem_q FMap.t

let empty = FMap.empty

let add = FMap.add

let remove = FMap.remove

let find id ctx =
  try FMap.find id ctx
  with _ ->
    let _ = Format.printf "unfound(%a)\n" Id.pp id in
    failwith "find"

let equal ctx1 ctx2 = FMap.equal (fun _ _ -> true) ctx1 ctx2

let scale n ctx = FMap.map (fun x -> { x with q = x.q * n }) ctx

let sum ctx1 ctx2 =
  FMap.merge
    (fun _ x1 x2 ->
      match (x1, x2) with
      | Some x1, Some x2 -> Some { x1 with q = x1.q + x2.q }
      | Some _, _ -> x1
      | _, Some _ -> x2
      | _ -> None)
    ctx1 ctx2

let sub ctx1 ctx2 =
  FMap.merge
    (fun _ x1 x2 ->
      match (x1, x2) with
      | Some x1, Some x2 -> Some { x1 with q = x1.q - x2.q }
      | Some _, _ -> x1
      | _, Some x2 -> Some { x2 with q = -x2.q }
      | _ -> None)
    ctx1 ctx2

let is_positive ctx = FMap.for_all (fun _ x -> x.q >= 0) ctx

let is_zero ctx = FMap.for_all (fun _ x -> x.q = 0) ctx
