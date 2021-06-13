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
           fun LListn =>
             fun l => (l' : Loc * ([l |-> (cons) l'] * (LListn) l')),
         n) : Nat -> Loc -> Linear)
  in
  let List := (fun n => (l : Loc * ((LList) n) l) : (n : Nat) -> Linear) in
  let Nil :=
    (fun _ => ((alloc) nil) ((left ()), refl((left ()),  UL)) : Unit ->
                                                                  (List) 0)
  in
  let Cons :=
    (fun _ =>
       fun ls =>
         let (l1, ls) := ls in
         let (l2, c) := ((alloc) (cons) l1)
           ((right l1), refl((right l1),  UL))
         in (l2, (l1, (c, ls))) : (n : Nat) -> (List) n -> (List) (n +1))
  in let main := (((Cons) 1) ((Cons) 0) (Nil) () : (List) 2) in main
complete
post_ctx := {
}
t  :=
  let (l1, ls) :=
    let (l1, ls) := ((alloc) (x : (Unit | Nat) * Eq(x, (left ()))))
      ((left ()), refl((left ()),  (Unit | Nat)))
    in
    let (l2, c) := ((alloc) (x : (Unit | Nat) * Eq(x, (right l1))))
      ((right l1), refl((right l1),  (Unit | Nat)))
    in (l2, (l1, (c, ls)))
  in
  let (l2, c) := ((alloc) (x : (Unit | Nat) * Eq(x, (right l1))))
    ((right l1), refl((right l1),  (Unit | Nat)))
  in (l2, (l1, (c, ls)))
ty :=
  (l : Nat *
    (l' : Nat *
      ([l |-> (x : (Unit | Nat) * Eq(x, (right l')))] *
        (l'0 : Nat *
          ([l' |-> (x : (Unit | Nat) * Eq(x, (right l'0)))] *
            [l'0 |-> (x : (Unit | Nat) * Eq(x, (left ())))])))))
