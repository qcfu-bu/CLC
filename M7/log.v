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
| DSucc#10 : (n_88 : TNat#2) -> ((TSNat#8 n_88)) -> (TSNat#8 (DS#4 n_88)).

Inductive TEq#11 : (A_90 : Type) -> (A_90) -> (A_90) -> Type :=
| DRefl#12 : (A_93 : Type) -> (x_94 : A_93) -> (TEq#11 A_93 x_94 x_94).

Inductive TSigma#13 : (A_95 : Type) -> (A_95 -> Type) -> Type :=
| DPair#14 : (A_98 : Type) ->
               (F_99 : A_98 -> Type) ->
                 (x_101 : A_98) -> ((F_99) x_101) -> (TSigma#13 A_98 F_99).

Inductive TTensor#15 : (Linear) -> (Linear) -> Linear :=
| DTPair#16 : (A_105 : Linear) ->
                (B_106 : Linear) ->
                  (A_105) -> (B_106) -> (TTensor#15 A_105 B_106).

Inductive TFTensor#17 : (A_109 : Type) -> (A_109 -> Linear) -> Linear :=
| DFPair#18 : (A_112 : Type) ->
                (F_113 : A_112 -> Linear) ->
                  (x_115 : A_112) ->
                    ((F_113) x_115) -> (TFTensor#17 A_112 F_113).

Definition Loc_117 := ((TNat#2) : Type).

Definition PtsTo_118 := DPtsTo#19.

Definition New_119 := DNew#20.

Definition Free_120 := DFree#21.

Definition Get_121 := DGet#22.

Definition Set_122 := DSet#23.

Definition main_123 :=
  ((let ft_124 := ((New_119) TNat#2) DO#3 in
    (match ft_124 in (TFTensor#17 L_126 F_127) return
       (TFTensor#17 L_126 F_127) -> TUnit#0 >> TUnit#0
     with
     | (DFPair#18 A_130 F_131 l_132 c_133) =>
       fun f_134 => (f_134) (DFPair#18 A_130 F_131 l_132 c_133)
     end) (Free_120) TNat#2) :
    TUnit#0).



v_ctx  := {
  main :0 (TUnit#0)::w
  Set :0
    ((A_337 : Type) ->
       (B_338 : Type) ->
         B_338 ->
           (l_340 : ((TNat#2) : Type)) ->
             ((DPtsTo#19) l_340) A_337 -> ((DPtsTo#19) l_340) B_338)::w
  Get :0
    ((A_342 : Type) ->
       (l_343 : ((TNat#2) : Type)) ->
         ((DPtsTo#19) l_343) A_342 ->
           (TFTensor#17 A_342 fun __345 => ((DPtsTo#19) l_343) A_342))::w
  Free :0
    ((A_346 : Type) ->
       (TFTensor#17 ((TNat#2) : Type) fun l_348 => ((DPtsTo#19) l_348) A_346) ->
         TUnit#0)::w
  New :0
    ((A_349 : Type) ->
       A_349 ->
         (TFTensor#17 ((TNat#2) : Type)
                        fun l_351 => ((DPtsTo#19) l_351) A_349))::w
  PtsTo :0 (((TNat#2) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
}

(match ((DNew#20) TNat#2) DO#3 in (TFTensor#17 L_447 F_448) return
   (TFTensor#17 L_447 F_448) -> TUnit#0 >> TUnit#0
 with
 | (DFPair#18 A_451 F_452 l_453 c_454) =>
   fun f_455 => (f_455) (DFPair#18 A_451 F_452 l_453 c_454)
 end) (DFree#21) TNat#2

