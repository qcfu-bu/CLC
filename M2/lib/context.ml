open Terms

module VarMap = Map.Make(
  struct
    type t = tvar
    let compare = Bindlib.compare_vars
  end)

type ctx = (term * int) VarMap.t

let empty = VarMap.empty

let add = VarMap.add

let remove = VarMap.remove

let find v ctx =
  try VarMap.find v ctx
  with _ -> failwith "unfound"
