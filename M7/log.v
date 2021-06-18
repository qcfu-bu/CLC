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
| DSucc#10 : (n_60 : TNat#2) -> ((TSNat#8 n_60)) -> (TSNat#8 (DS#4 n_60)).

Inductive TEq#11 (A_62 : Type) : (A_62) -> (A_62) -> Type :=
| DRefl#12 (A_65 : Type) : (x_66 : A_65) -> (TEq#11 A_65 x_66 x_66).

Inductive TSigma#13 (A_67 : Type) (F_68 : A_67 -> Type) : Type :=
| DPair#14 (A_70 : Type)
             (F_71 : A_70 -> Type)
               : (x_73 : A_70) -> ((F_71) x_73) -> (TSigma#13 A_70 F_71).

Inductive TTensor#15 (A_75 : Linear) (B_76 : Linear) : Linear :=
| DTPair#16 (A_77 : Linear)
              (B_78 : Linear) : (A_77) -> (B_78) -> (TTensor#15 A_77 B_78).

Inductive TFTensor#17 (A_81 : Type) (F_82 : A_81 -> Linear) : Linear :=
| DFPair#18 (A_84 : Type)
              (F_85 : A_84 -> Linear)
                : (x_87 : A_84) -> ((F_85) x_87) -> (TFTensor#17 A_84 F_85).

Definition Loc_89 := ((TNat#2) : Type).

Definition PtsTo_90 := DPtsTo#19.

Definition New_91 := DNew#20.

Definition Free_92 := DFree#21.

Definition Get_93 := DGet#22.

Definition Set_94 := DSet#23.

Definition prev_95 :=
  ((fun n_96 x_97 =>
      match x_97 in (TSNat#8 n_99) return
        match n_99 with
        | (DO#3 ) => TUnit#0
        | (DS#4 n_100) => (TSNat#8 n_100)
        end
      with
      | (DZero#9 ) => Dtt#1
      | (DSucc#10 __101 x_102) => x_102
      end) :
    (n_103 : TNat#2) -> (x_104 : (TSNat#8 (DS#4 n_103))) -> (TSNat#8 n_103)).

Definition main_105 :=
  ((let ft_106 := ((New_91) TNat#2) DO#3 in
    match ft_106 with
    | (DFPair#18 l_107 c_108) => ((Free_92) TNat#2) (DFPair#18 l_107 c_108)
    end) : TUnit#0).



v_ctx  := {
  main :0 (TUnit#0)::w
  prev :0
    ((n_364 : TNat#2) -> (x_365 : (TSNat#8 (DS#4 n_364))) -> (TSNat#8 n_364))::w
  Set :0
    ((A_366 : Type) ->
       (B_367 : Type) ->
         B_367 ->
           (l_369 : ((TNat#2) : Type)) ->
             ((DPtsTo#19) l_369) A_366 -> ((DPtsTo#19) l_369) B_367)::w
  Get :0
    ((A_371 : Type) ->
       (l_372 : ((TNat#2) : Type)) ->
         ((DPtsTo#19) l_372) A_371 ->
           (TFTensor#17 A_371 fun __374 => ((DPtsTo#19) l_372) A_371))::w
  Free :0
    ((A_375 : Type) ->
       (TFTensor#17 ((TNat#2) : Type) fun l_377 => ((DPtsTo#19) l_377) A_375) ->
         TUnit#0)::w
  New :0
    ((A_378 : Type) ->
       A_378 ->
         (TFTensor#17
           ((TNat#2) : Type) fun l_380 => ((DPtsTo#19) l_380) A_378))::w
  PtsTo :0 (((TNat#2) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
}

match ((DNew#20) TNat#2) DO#3 with
| (DFPair#18 l_466 c_467) => ((DFree#21) TNat#2) (DFPair#18 l_466 c_467)
end

