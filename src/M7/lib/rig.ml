open Format

type rig =
  | Zero
  | One 
  | W

let ( + ) r1 r2 =
  match r1, r2 with
  | Zero, _  -> r2
  | _, Zero  -> r1
  | One, One -> W
  | W, _     -> W
  | _, W     -> W

let ( * ) r1 r2 =
  match r1, r2 with
  | Zero, _  -> Zero
  | _, Zero  -> Zero
  | One, One -> One
  | W, _     -> W
  | _, W     -> W

let ( = ) r1 r2 = r1 = r2

let ( <= ) r1 r2 =
  match r1, r2 with
  | Zero, Zero -> true
  | Zero, W    -> true
  | One, One   -> true
  | One, W     -> true
  | W, W       -> true
  | _          -> false

let min r1 r2 =
  if r1 <= r2 then r1 else r2

let pp fmt = function
  | Zero -> fprintf fmt "0"
  | One -> fprintf fmt "1"
  | W -> fprintf fmt "w"

