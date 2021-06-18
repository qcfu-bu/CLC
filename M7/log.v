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
| DSucc#10 : (n_57 : TNat#2) -> ((TSNat#8 n_57)) -> (TSNat#8 (DS#4 n_57)).

Inductive TEq#11 (A_59 : Type) : (A_59) -> (A_59) -> Type :=
| DRefl#12 (A_62 : Type) : (x_63 : A_62) -> (TEq#11 A_62 x_63 x_63).

Inductive TSigma#13 (A_64 : Type) (F_65 : A_64 -> Type) : Type :=
| DPair#14 (A_67 : Type)
             (F_68 : A_67 -> Type)
               : (x_70 : A_67) -> ((F_68) x_70) -> (TSigma#13 A_67 F_68).

Inductive TTensor#15 (A_72 : Linear) (B_73 : Linear) : Linear :=
| DTPair#16 (A_74 : Linear)
              (B_75 : Linear) : (A_74) -> (B_75) -> (TTensor#15 A_74 B_75).

Inductive TFTensor#17 (A_78 : Type) (F_79 : A_78 -> Linear) : Linear :=
| DFPair#18 (A_81 : Type)
              (F_82 : A_81 -> Linear)
                : (x_84 : A_81) -> ((F_82) x_84) -> (TFTensor#17 A_81 F_82).

Definition Loc_86 := ((TNat#2) : Type).

Definition PtsTo_87 := DPtsTo#19.

Definition New_88 := DNew#20.

Definition Free_89 := DFree#21.

Definition Get_90 := DGet#22.

Definition Set_91 := DSet#23.

Definition main_92 :=
  ((let ft_93 := ((New_88) TNat#2) DO#3 in
    match ft_93 with
    | (DFPair#18 l_94 c_95) => ((Free_89) TNat#2) (DFPair#18 l_94 c_95)
    end) : TUnit#0).



v_ctx  := {
  main :0 (TUnit#0)::w
  Set :0
    ((A_267 : Type) ->
       (B_268 : Type) ->
         B_268 ->
           (l_270 : ((TNat#2) : Type)) ->
             ((DPtsTo#19) l_270) A_267 -> ((DPtsTo#19) l_270) B_268)::w
  Get :0
    ((A_272 : Type) ->
       (l_273 : ((TNat#2) : Type)) ->
         ((DPtsTo#19) l_273) A_272 ->
           (TFTensor#17 A_272 fun __275 => ((DPtsTo#19) l_273) A_272))::w
  Free :0
    ((A_276 : Type) ->
       (TFTensor#17 ((TNat#2) : Type) fun l_278 => ((DPtsTo#19) l_278) A_276) ->
         TUnit#0)::w
  New :0
    ((A_279 : Type) ->
       A_279 ->
         (TFTensor#17
           ((TNat#2) : Type) fun l_281 => ((DPtsTo#19) l_281) A_279))::w
  PtsTo :0 (((TNat#2) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
}

match ((DNew#20) TNat#2) DO#3 with
| (DFPair#18 l_364 c_365) => ((DFree#21) TNat#2) (DFPair#18 l_364 c_365)
end

