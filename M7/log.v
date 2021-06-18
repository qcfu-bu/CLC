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
| DSucc#10 : (n_67 : TNat#2) -> ((TSNat#8 n_67)) -> (TSNat#8 (DS#4 n_67)).

Inductive TEq#11 (A_69 : Type) : (A_69) -> (A_69) -> Type :=
| DRefl#12 (A_72 : Type) : (x_73 : A_72) -> (TEq#11 A_72 x_73 x_73).

Inductive TSigma#13 (A_74 : Type) (F_75 : A_74 -> Type) : Type :=
| DPair#14 (A_77 : Type)
             (F_78 : A_77 -> Type)
               : (x_80 : A_77) -> ((F_78) x_80) -> (TSigma#13 A_77 F_78).

Inductive TTensor#15 (A_82 : Linear) (B_83 : Linear) : Linear :=
| DTPair#16 (A_84 : Linear)
              (B_85 : Linear) : (A_84) -> (B_85) -> (TTensor#15 A_84 B_85).

Inductive TFTensor#17 (A_88 : Type) (F_89 : A_88 -> Linear) : Linear :=
| DFPair#18 (A_91 : Type)
              (F_92 : A_91 -> Linear)
                : (x_94 : A_91) -> ((F_92) x_94) -> (TFTensor#17 A_91 F_92).

Inductive TSN#19 (N_96 : TNat#2) : Type :=
| Dsn#20 (N_97 : TNat#2) : (n_98 : TNat#2) -> (TSN#19 N_97).

Definition bad_99 := (((Dsn#20 (DS#4 DO#3))) : (TSN#19 (DS#4 DO#3))).

Definition Loc_100 := ((TNat#2) : Type).

Definition PtsTo_101 := DPtsTo#21.

Definition New_102 := DNew#22.

Definition Free_103 := DFree#23.

Definition Get_104 := DGet#24.

Definition Set_105 := DSet#25.

Definition prev_106 :=
  ((fun n_107 x_108 =>
      match x_108 in (TSNat#8 n_110) return
        match n_110 with
        | (DO#3 ) => TUnit#0
        | (DS#4 n_111) => (TSNat#8 n_111)
        end
      with
      | (DZero#9 ) => Dtt#1
      | (DSucc#10 __112 x_113) => x_113
      end) :
    (n_114 : TNat#2) -> (x_115 : (TSNat#8 (DS#4 n_114))) -> (TSNat#8 n_114)).

Definition main_116 :=
  ((let ft_117 := ((New_102) TNat#2) DO#3 in
    match ft_117 in (TFTensor#17 L_119 F_120) return TUnit#0 with
    | (DFPair#18 l_121 c_122) => ((Free_103) TNat#2) (DFPair#18 l_121 c_122)
    end) : TUnit#0).



v_ctx  := {
  main :0 (TUnit#0)::w
  prev :0
    ((n_402 : TNat#2) -> (x_403 : (TSNat#8 (DS#4 n_402))) -> (TSNat#8 n_402))::w
  Set :0
    ((A_404 : Type) ->
       (B_405 : Type) ->
         B_405 ->
           (l_407 : ((TNat#2) : Type)) ->
             ((DPtsTo#21) l_407) A_404 -> ((DPtsTo#21) l_407) B_405)::w
  Get :0
    ((A_409 : Type) ->
       (l_410 : ((TNat#2) : Type)) ->
         ((DPtsTo#21) l_410) A_409 ->
           (TFTensor#17 A_409 fun __412 => ((DPtsTo#21) l_410) A_409))::w
  Free :0
    ((A_413 : Type) ->
       (TFTensor#17 ((TNat#2) : Type) fun l_415 => ((DPtsTo#21) l_415) A_413) ->
         TUnit#0)::w
  New :0
    ((A_416 : Type) ->
       A_416 ->
         (TFTensor#17
           ((TNat#2) : Type) fun l_418 => ((DPtsTo#21) l_418) A_416))::w
  PtsTo :0 (((TNat#2) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  bad :0 ((TSN#19 (DS#4 DO#3)))::w
}

match ((DNew#22) TNat#2) DO#3 in (TFTensor#17 L_506 F_507) return TUnit#0
with
| (DFPair#18 l_508 c_509) => ((DFree#23) TNat#2) (DFPair#18 l_508 c_509)
end

