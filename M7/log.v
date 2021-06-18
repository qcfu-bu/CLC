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
| DSucc#10 : (n_74 : TNat#2) -> ((TSNat#8 n_74)) -> (TSNat#8 (DS#4 n_74)).

Inductive TEq#11 (A_76 : Type) : (A_76) -> (A_76) -> Type :=
| DRefl#12 (A_79 : Type) : (x_80 : A_79) -> (TEq#11 A_79 x_80 x_80).

Inductive TSigma#13 (A_81 : Type) (F_82 : A_81 -> Type) : Type :=
| DPair#14 (A_84 : Type)
             (F_85 : A_84 -> Type)
               : (x_87 : A_84) -> ((F_85) x_87) -> (TSigma#13 A_84 F_85).

Inductive TTensor#15 (A_89 : Linear) (B_90 : Linear) : Linear :=
| DTPair#16 (A_91 : Linear)
              (B_92 : Linear) : (A_91) -> (B_92) -> (TTensor#15 A_91 B_92).

Inductive TFTensor#17 (A_95 : Type) (F_96 : A_95 -> Linear) : Linear :=
| DFPair#18 (A_98 : Type)
              (F_99 : A_98 -> Linear)
                : (x_101 : A_98) -> ((F_99) x_101) -> (TFTensor#17 A_98 F_99).

Inductive TSN#19 (N_103 : TNat#2) : Type :=
| Dsn#20 (N_104 : TNat#2) : (n_105 : TNat#2) -> (TSN#19 N_104).

Definition bad_106 := (((Dsn#20 (DS#4 DO#3))) : (TSN#19 (DS#4 DO#3))).

Definition Loc_107 := ((TNat#2) : Type).

Axiom PtsTo_108 : Loc_107 -> Type -> Linear.

Definition Ptr_111 :=
  ((fun A_112 => (TFTensor#17 Loc_107 fun l_113 => ((PtsTo_108) l_113) A_112)) :
    (A_114 : Type) -> Linear).

Axiom New_115 : (A_116 : Type) -> A_116 -> (Ptr_111) A_116.

Axiom Free_118 : (A_119 : Type) -> (Ptr_111) A_119 -> TUnit#0.

Axiom Get_121 :
  (A_122 : Type) ->
    (l_123 : Loc_107) ->
      ((PtsTo_108) l_123) A_122 ->
        (TFTensor#17 A_122 fun __125 => ((PtsTo_108) l_123) A_122).

Axiom Set_126 :
  (A_127 : Type) ->
    (B_128 : Type) ->
      B_128 ->
        (l_130 : Loc_107) ->
          ((PtsTo_108) l_130) A_127 -> ((PtsTo_108) l_130) B_128.

Definition prev_132 :=
  ((fun n_133 x_134 =>
      match x_134 in (TSNat#8 n_136) return
        match n_136 with
        | (DO#3 ) => TUnit#0
        | (DS#4 n_137) => (TSNat#8 n_137)
        end
      with
      | (DZero#9 ) => Dtt#1
      | (DSucc#10 __138 x_139) => x_139
      end) :
    (n_140 : TNat#2) -> (x_141 : (TSNat#8 (DS#4 n_140))) -> (TSNat#8 n_140)).

Definition n_142 := ((((New_115) TNat#2) DO#3) : (Ptr_111) TNat#2).

Definition Assign_143 :=
  ((fun A_144 ptr_145 x_146 =>
      match ptr_145 with
      | (DFPair#18 l_147 c_148) =>
        let c_149 := (((((Set_126) A_144) A_144) x_146) l_147) c_148 in
        (DFPair#18 l_147 c_149)
      end) :
    (A_150 : Type) ->
      (ptr_151 : (Ptr_111) A_150) -> (x_152 : A_150) -> (Ptr_111) A_150).

Definition main_153 :=
  ((match n_142 with
    | (DFPair#18 l_154 c_155) =>
      let xc_156 := (((Get_121) TNat#2) l_154) c_155 in
      match xc_156 with
      | (DFPair#18 x_157 c_158) =>
        let __159 := ((Free_118) TNat#2) (DFPair#18 l_154 c_158) in x_157
      end
    end) : TNat#2).



