checking
t  :=
  let Loc := (Nat : Type) in
  let Ptr := (fun A => (x : Loc * [x |-> A]) : Type -> Linear) in
  let Alloc := (fun A x => ((alloc) A) x : (A : Type) -> A -> (Ptr) A) in
  let Get :=
    (fun A ptr =>
       let (l, c) := ptr in let (x, c) := (((get) A) l) c in (x, (l, c)) :
      (A : Type) -> (Ptr) A -> (A * (Ptr) A))
  in
  let Set :=
    (fun A ptr x =>
       let (l, c) := ptr in let c := (((((set) A) A) l) c) x in (l, c) :
      (A : Type) -> (Ptr) A -> A >> (Ptr) A)
  in
  let Free :=
    (fun A ptr => let (l, c) := ptr in (((free) A) l) c :
      (A : Type) -> (Ptr) A -> Unit)
  in
  let main :=
    (let ptr := ((Alloc) Nat) 1 in
     let (m, ptr) := ((Get) Nat) ptr in
     let ptr := (((Set) Nat) ptr) 2 in
     let (n, ptr) := ((Get) Nat) ptr in let _ := ((Free) Nat) ptr in (m, n) :
      (Nat * Nat))
  in main
complete
post_ctx := { }
ty := (Nat * Nat)
evaluate
t  := (1, 2)
heap := [ ]
