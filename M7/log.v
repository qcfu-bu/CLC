Inductive TNat#0 : Type :=
| DO#1 : TNat#0
| DS#2 : (TNat#0) -> TNat#0.

Inductive TList#3 : (Type) -> Type :=
| Dnil#4 : (A_26 : Type) -> (TList#3 A_26)
| Dcons#5 : (A_27 : Type) ->
              (A_27 -> A_27) -> ((TList#3 A_27)) -> (TList#3 A_27).

Definition plus_31 :=
  ((fix plus_32 x_33 y_34 =>
      match x_33 with
      | (DO#1 ) => y_34
      | (DS#2 x_35) => (DS#2 ((plus_32) x_35) y_34)
      end) :
    (x_36 : TNat#0) -> (y_37 : TNat#0) -> TNat#0).

Definition count_38 :=
  ((fix count_39 A_40 ls_41 =>
      match ls_41 with
      | (Dnil#4 __42) => DO#1
      | (Dcons#5 __43 __44 ls_45) => (DS#2 ((count_39) A_40) ls_45)
      end) :
    (A_46 : Type) -> (ls_47 : (TList#3 A_46)) -> TNat#0).

Definition count'_48 :=
  ((fix count'_49 A_50 ls_51 =>
      match ls_51 as x_52 in (TList#3 A_53) return
        match A_53 with
        | (DO#1 ) => (TList#3 A_53)
        | (DS#2 x_54) => (TList#3 x_54)
        end
      with
      | (Dnil#4 __55) => DO#1
      | (Dcons#5 __56 __57 ls_58) => (DS#2 ((count'_49) A_50) ls_58)
      end) :
    (A_59 : Type) -> (ls_60 : (TList#3 A_59)) -> TNat#0).

Definition ls_61 :=
  (((Dcons#5 TNat#0 DO#1 (Dnil#4 TNat#0))) : (TList#3 TNat#0)).

Definition main_62 :=
  ((((plus_31) ((plus_31) (DS#2 DO#1)) (DS#2 DO#1)) ((count_38) TNat#0) ls_61) :
    TNat#0).



(DS#2 (DS#2 (DS#2 DO#1)))

