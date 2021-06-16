magicMatch(x_3)
Inductive T(Nat#0) : Base(Type) :=
| D(O#1) : Base(T(Nat#0))
| D(S#2) : Bind(T(Nat#0) -> Base(T(Nat#0))).

Definition plus_7 :=
  ((fix plus_8 x_9 y_10 =>
      match x_9 with
      | (D(O#1) ) => y_10
      | (D(S#2) x_11) => DCons(D(S#2) (App((App((plus_8) x_11)) y_10)))
      end) :
    (x_12 : T(Nat#0)) -> (y_13 : T(Nat#0)) -> T(Nat#0)).

Definition main_14 := ((D(O#1)) : T(Nat#0)).



D(O#1)

