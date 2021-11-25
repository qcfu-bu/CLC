
type ring =
  | Zero
  | One
  | W

let ( + ) r1 r2 =
  match r1, r2 with
  | Zero, _ -> r2
  | _, Zero -> r1
  | W, _ -> W
  | _, W -> W
  | One, One -> W

let ( - ) r1 r2 =
  match r1, r2 with
  | _, Zero -> r1
  | Zero, _ -> failwith "subtraction"
  | W, _ -> W
  | _, W -> failwith "subtraction"
  | One, One -> Zero

let ( * ) r1 r2 =
  match r1, r2 with
  | Zero, _ -> Zero
  | _, Zero -> Zero
  | W, _ -> W
  | _, W -> W
  | One, One -> One

let ( = ) r1 r2 = r1 = r2

let ( <= ) r1 r2 =
  match r1, r2 with
  | Zero, Zero -> true
  | Zero, One  -> true
  | Zero, W    -> true
  | One,  Zero -> false
  | One,  One  -> true
  | One,  W    -> true
  | W,    Zero -> false
  | W,    One  -> false
  | W,    W    -> true

let z = Zero
let o = One
let w = W

let pp fmt r = 
  Format.fprintf fmt "%s" (
    match r with
    | Zero -> "0"
    | One  -> "1"
    | W    -> "w")