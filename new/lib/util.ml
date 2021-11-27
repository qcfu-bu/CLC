let rec zip ls1 ls2 =
  match ls1, ls2 with
  | x1 :: ls1, x2 :: ls2 -> (x1, x2) :: zip ls1 ls2
  | [], [] -> []
  | _ -> failwith "zip unequal length"

let rec unzip ls =
  match ls with
  | (x, y) :: ls ->
    let xs, ys = unzip ls in
    (x :: xs, y :: ys)
  | [] -> ([], [])

let assert_msg cond msg = 
  if cond then ()
  else (prerr_endline msg; assert false)

let failwith msg =
  (prerr_endline msg; assert false)