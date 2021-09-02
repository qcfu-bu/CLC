
open Format

let pp pp (fmt : formatter) ls =
  List.iter (fun x ->
    fprintf fmt "%a@." pp x) ls