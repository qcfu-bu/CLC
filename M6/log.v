checking
t  :=
  let Loc := (Nat : Type) in
  let Ptr := (fun A => (x : Loc * [x |-> A]) : Type -> Linear) in
  let nbox := (((alloc) Nat) 1 : (Ptr) Nat) in
  let main :=
    (let (l, c) := nbox in
     let (n, c) := (((get) Nat) l) c in
     let c := (((((set) Nat) Nat) l) c) 2 in
     let (n, c) := (((get) Nat) l) c in let _ := (((free) Nat) l) c in n :
      Nat)
  in main
complete
post_ctx := {
}
t  := 2
ty := Nat
