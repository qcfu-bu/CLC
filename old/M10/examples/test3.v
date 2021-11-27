Inductive session : Type :=
| SEND : Type -> session -> session
| RECV : Type -> session -> session
| END : session.

Axiom channel : session -> Linear.
Axiom open : (ss : session) -> channel ss.
Axiom close : channel END -> Unit.
Axiom send : (A : Type) -> A -> (ss : session) -> channel (SEND A ss) -> channel ss.
Axiom recv : (A : Type) -> (ss : session) -> channel (RECV A ss) -> [A | channel ss].

Inductive ilist (A : Type) : Nat -> Type :=
| nil  : ilist A 0
| cons : A -> (n : Nat) -> ilist A n -> ilist A (S n).

Definition main : Unit :=
  let ss := SEND (ilist Nat 2) (RECV (ilist Nat 8) (SEND Bool END)) in
  let send_msg : ilist Nat 2 := (cons 1 _ (cons 2 _ nil)) in
  let ch := open ss in
  let ch := send _ send_msg _ ch in
  let [ recv_msg, ch ] := recv _ _ ch in
  let ch := send _ true _ ch in
  close ch.
