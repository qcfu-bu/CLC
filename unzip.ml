
let unzip ls =
  let rec rev ls acc =
    match ls with
    | x :: ls -> rev ls (x :: acc)
    | [] -> acc
  in
  let rec aux ls l r =
    match ls with
    | (x, y) :: ls -> aux ls (x :: l) (y :: r)
    | [] -> (rev l [], rev r [])
  in
  aux ls [] []