Inductive session : U :=
| SEND : U -> session -> session
| RECV : U -> session -> session
| END : session.

Axiom channel : session -> L.
Axiom open : (ss : session) -> channel ss.
Axiom close : channel END -> unit.
Axiom send : (A : U) -> A -> (ss : session) -> channel (SEND A ss) -> channel ss.
Axiom recv : (A : U) -> (ss : session) -> channel (RECV A ss) -> [A | channel ss].

Inductive ilist (A : U) : nat -> U :=
| nil  : ilist A 0
| cons : A -> (n : nat) -> ilist A n -> ilist A (S n).

Definition main : unit :=
  let ss := SEND (ilist nat 2) (RECV (ilist nat 8) (SEND bool END)) in
  let send_msg : ilist nat 2 := (cons 1 _ (cons 2 _ nil)) in
  let ch := open ss in
  let ch := send _ send_msg _ ch in
  let [ recv_msg, ch ] := recv _ _ ch in
  let ch := send _ true _ ch in
  close ch.
