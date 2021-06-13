checking
t  :=
  let Loc := (Nat : Type) in
  let UL := (fun A => (Unit | (A * Loc)) : Type -> Type) in
  let nil := (fun A => (x : (UL) A * Eq(x, (left ()))) : Type -> Type) in
  let cons :=
    (fun A => fun l => (x : (UL) A * (a : A * Eq(x, (right (a, l))))) :
      Type -> Loc -> Type)
  in
  let LList :=
    (fun A =>
       fun n =>
         iter(fun _ => Loc -> Linear, fun l => [l |-> (nil) A],
           fun n =>
             fun LListN =>
               fun l => (l' : Loc * ([l |-> ((cons) A) l'] * (LListN) l')),
           n) :
      Type -> Nat -> Loc -> Linear)
  in
  let List :=
    (fun A => fun n => (l : Loc * (((LList) A) n) l) :
      Type -> (n : Nat) -> Linear)
  in
  let Nil :=
    (fun A => ((alloc) (nil) A) ((left ()), refl((left ()),  (UL) A)) :
      (A : Type) -> ((List) A) 0)
  in
  let Cons :=
    (fun A =>
       fun a =>
         fun _ =>
           fun ls =>
             let (l1, ls) := ls in
             let (l2, c) :=
               ((alloc) ((cons) A) l1)
                 ((right (a, l1)), (a, refl((right (a, l1)),  (UL) A)))
             in (l2, (l1, (c, ls))) :
      (A : Type) -> A -> (n : Nat) -> ((List) A) n -> ((List) A) (n +1))
  in
  let Uncons :=
    (fun A =>
       fun _ =>
         fun ls =>
           let (l2, ls) := ls in
           let (l1, ls) := ls in
           let (c, ls) := ls in
           let _ := ((free) ((cons) A) l1) (l2, c) in (l1, ls) :
      (A : Type) -> (n : Nat) -> ((List) A) (n +1) -> ((List) A) n)
  in
  let MakeList :=
    (fun A =>
       fun a =>
         fun n =>
           iter(fun n => ((List) A) n, (Nil) A,
             fun n => fun lsN => ((((Cons) A) a) n) lsN, n) :
      (A : Type) -> A -> (n : Nat) -> ((List) A) n)
  in
  let FreeList :=
    (fun A =>
       fun n =>
         iter(fun n => ((List) A) n -> Unit, fun ls => ((free) (nil) A) ls,
           fun n =>
             fun FreeN =>
               fun ls => let ls := (((Uncons) A) n) ls in (FreeN) ls,
           n) :
      (A : Type) -> (n : Nat) -> ((List) A) n -> Unit)
  in let main := (() : Unit) in main
complete
post_ctx := {
}
t  := ()
ty := Unit
