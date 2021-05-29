type ring =
  | N of int
  | W

let ( + ) r1 r2 =
  match r1, r2 with N n1, N n2 -> N (n1 + n2) | W, _ -> W | _, W -> W
;;

let ( * ) r1 r2 =
  match r1, r2 with N n1, N n2 -> N (n1 * n2) | W, _ -> W | _, W -> W
;;
