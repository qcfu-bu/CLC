
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