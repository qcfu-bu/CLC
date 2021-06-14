checking
t  :=
  let Loc := (Nat : Type) in
  let null := (Unit : Type) in
  let box :=
    (fun A l => (a : A * (l' : Loc * Eq(l, l'))) : Type -> Loc -> Type)
  in
  let LList :=
    (fun A n =>
       iter(fun _ => Loc -> Linear, fun l => [l |-> null],
         fun n LListN l => (l' : Loc * ([l |-> ((box) A) l'] * (LListN) l')),
         n) :
      Type -> Nat -> Loc -> Linear)
  in
  let List :=
    (fun A n => (l : Loc * (((LList) A) n) l) : Type -> (n : Nat) -> Linear)
  in
  let Nil := (fun A => ((alloc) null) () : (A : Type) -> ((List) A) 0) in
  let Cons :=
    (fun A a _ ls =>
       let (l1, ls) := ls in
       let (l2, c) := ((alloc) ((box) A) l1) (a, (l1, refl(l1,  Loc))) in
       (l2, (l1, (c, ls))) :
      (A : Type) -> A -> (n : Nat) -> ((List) A) n -> ((List) A) (n +1))
  in
  let Uncons :=
    (fun A _ ls =>
       let (l2, ls) := ls in
       let (l1, ls) := ls in
       let (c, ls) := ls in
       let (bx, c) := (((get) ((box) A) l1) l2) c in
       let _ := (((free) ((box) A) l1) l2) c in
       let (a, _) := bx in (a, (l1, ls)) :
      (A : Type) -> (n : Nat) -> ((List) A) (n +1) -> (A * ((List) A) n))
  in
  let MakeList :=
    (fun A a n =>
       iter(fun n => ((List) A) n, (Nil) A,
         fun n lsN => ((((Cons) A) a) n) lsN, n) :
      (A : Type) -> A -> (n : Nat) -> ((List) A) n)
  in
  let FreeList :=
    (fun A n =>
       iter(fun n => ((List) A) n -> Unit,
         fun ls => let (l, ls) := ls in (((free) null) l) ls,
         fun n FreeN ls => let (_, ls) := (((Uncons) A) n) ls in (FreeN) ls,
         n) :
      (A : Type) -> (n : Nat) -> ((List) A) n -> Unit)
  in
  let main :=
    (let xs := (((MakeList) Nat) 3) 10 in
     let (x, xs) := (((Uncons) Nat) 9) xs in
     let _ := (((FreeList) Nat) 9) xs in x : Nat)
  in main
complete
post_ctx := { }
ty := Nat
evaluate
t  := 3
heap := [ ]
