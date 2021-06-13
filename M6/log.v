checking
t  :=
  let Loc := (Nat : Type) in
  let UL := ((Unit | Loc) : Type) in
  let nil := ((x : UL * Eq(x, (left ()))) : Type) in
  let cons := (fun l => (x : UL * Eq(x, (right l))) : Loc -> Type) in
  let LList :=
    (fun n =>
       iter(fun _ => Loc -> Linear, fun l => [l |-> nil],
         fun n =>
           fun LListN =>
             fun l => (l' : Loc * ([l |-> (cons) l'] * (LListN) l')),
         n) :
      Nat -> Loc -> Linear)
  in
  let List := (fun n => (l : Loc * ((LList) n) l) : (n : Nat) -> Linear) in
  let Nil :=
    (fun _ => ((alloc) nil) ((left ()), refl((left ()),  UL)) :
      Unit -> (List) 0)
  in
  let Cons :=
    (fun _ =>
       fun ls =>
         let (l1, ls) := ls in
         let (l2, c) :=
           ((alloc) (cons) l1) ((right l1), refl((right l1),  UL))
         in (l2, (l1, (c, ls))) :
      (n : Nat) -> (List) n -> (List) (n +1))
  in
  let Uncons :=
    (fun _ =>
       fun ls =>
         let (l2, ls) := ls in
         let (l1, ls) := ls in
         let (c, ls) := ls in let _ := ((free) (cons) l1) (l2, c) in (l1, ls) :
      (n : Nat) -> (List) (n +1) -> (List) n)
  in
  let FreeList :=
    (fun n =>
       iter(fun n => (List) n -> Unit, fun ls => ((free) nil) ls,
         fun n =>
           fun FreeN => fun ls => let ls := ((Uncons) n) ls in (FreeN) ls,
         n) :
      (n : Nat) -> (List) n -> Unit)
  in
  let main :=
    (let ls := ((Cons) 1) ((Cons) 0) (Nil) () in ((FreeList) 2) ls : Unit)
  in main
complete
post_ctx := {
}
t  :=
  ((free) (x : (Unit | Nat) * Eq(x, (left ()))))
    let (l2, ls) :=
      let (l2, ls) :=
        let (l1, ls) :=
          let (l1, ls) :=
            ((alloc) (x : (Unit | Nat) * Eq(x, (left ()))))
              ((left ()), refl((left ()),  (Unit | Nat)))
          in
          let (l2, c) :=
            ((alloc) (x : (Unit | Nat) * Eq(x, (right l1))))
              ((right l1), refl((right l1),  (Unit | Nat)))
          in (l2, (l1, (c, ls)))
        in
        let (l2, c) :=
          ((alloc) (x : (Unit | Nat) * Eq(x, (right l1))))
            ((right l1), refl((right l1),  (Unit | Nat)))
        in (l2, (l1, (c, ls)))
      in let (l1, ls) := ls in let (c, ls) := ls in (l1, ls)
    in let (l1, ls) := ls in let (c, ls) := ls in (l1, ls)
ty := Unit
