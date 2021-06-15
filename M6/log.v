checking
t  :=
  let Loc := (Nat : Type) in
  let Ref := (fun A => (x : Loc * [x |-> A]) : Type -> Linear) in
  let New := (fun A x => ((alloc) A) x : (A : Type) -> A -> (Ref) A) in
  let Get :=
    (fun A ref =>
       let (l, c) := ref in let (x, c) := (((get) A) l) c in (x, (l, c)) :
      (A : Type) -> (Ref) A -> (A * (Ref) A))
  in
  let Assign :=
    (fun A ref x =>
       let (l, c) := ref in let c := (((((set) A) A) l) c) x in (l, c) :
      (A : Type) -> (Ref) A -> A >> (Ref) A)
  in
  let Free :=
    (fun A ref => let (l, c) := ref in (((free) A) l) c :
      (A : Type) -> (Ref) A -> Unit)
  in
  let main :=
    (7 :
      let ref := ((New) Nat) 2 in
      let ref := (((Assign) Nat) ref) 1 in let _ := ((Free) Nat) ref in Nat)
  in main
complete
post_ctx := { }
ty := Nat
evaluate
t  := 7
heap := [ ]
