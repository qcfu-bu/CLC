Inductive TUnit#0 : Type :=
| Dtt#1 : TUnit#0.

Inductive TNat#2 : Type :=
| DO#3 : TNat#2
| DS#4 : (TNat#2) -> TNat#2.

Inductive TBool#5 : Type :=
| Dtrue#6 : TBool#5
| Dfalse#7 : TBool#5.

Inductive TSNat#8 : (TNat#2) -> Type :=
| DZero#9 : (TSNat#8 DO#3)
| DSucc#10 : (n_19 : TNat#2) -> ((TSNat#8 n_19)) -> (TSNat#8 (DS#4 n_19)).

Definition neg_21 :=
  ((fun b_22 =>
      match b_22 with
      | (Dtrue#6 ) => Dfalse#7
      | (Dfalse#7 ) => Dtrue#6
      end) :
    (b_23 : TBool#5) -> TBool#5).

Definition add_24 :=
  ((fix add_25 x_26 y_27 =>
      match x_26 with
      | (DO#3 ) => y_27
      | (DS#4 x_28) => (DS#4 ((add_25) x_28) y_27)
      end) :
    (x_29 : TNat#2) -> (y_30 : TNat#2) -> TNat#2).

Definition pred_31 :=
  ((fun n_32 x_33 =>
      match x_33 in (TSNat#8 n_35) return
        match n_35 with
        | (DO#3 ) => TUnit#0
        | (DS#4 n_36) => (TSNat#8 n_36)
        end
      with
      | (DZero#9 ) => Dtt#1
      | (DSucc#10 __37 x_38) => x_38
      end) :
    (n_39 : TNat#2) -> (x_40 : (TSNat#8 (DS#4 n_39))) -> (TSNat#8 n_39)).

Definition One_41 := (((DSucc#10 DO#3 DZero#9)) : (TSNat#8 (DS#4 DO#3))).

Definition main_42 := ((((pred_31) DO#3) One_41) : (TSNat#8 DO#3)).



v_ctx  := {
  main :0 ((TSNat#8 DO#3))::w
  One :0 ((TSNat#8 (DS#4 DO#3)))::w
  pred :0
    ((n_134 : TNat#2) -> (x_135 : (TSNat#8 (DS#4 n_134))) -> (TSNat#8 n_134))::w
  add :0 ((x_136 : TNat#2) -> (y_137 : TNat#2) -> TNat#2)::w
  neg :0 ((b_138 : TBool#5) -> TBool#5)::w
}

DZero#9

