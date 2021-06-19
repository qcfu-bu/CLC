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
| DSucc#10 : (n_2 : TNat#2) -> ((TSNat#8 n_2)) -> (TSNat#8 (DS#4 n_2)).

Inductive TEq#11 (A_3 : Type) : (A_3) -> (A_3) -> Type :=
| DRefl#12 (A_3 : Type) : (x_5 : A_3) -> (TEq#11 A_3 x_5 x_5).

Inductive TSigma#13 (A_6 : Type) (F_7 : A_6 -> Type) : Type :=
| DPair#14 (A_6 : Type)
             (F_7 : A_6 -> Type)
               : (x_9 : A_6) -> ((F_7) x_9) -> (TSigma#13 A_6 F_7).

Inductive TTensor#15 (A_10 : Linear) (B_11 : Linear) : Linear :=
| DTPair#16 (A_10 : Linear)
              (B_11 : Linear) : (A_10) -> (B_11) -> (TTensor#15 A_10 B_11).

Inductive TFTensor#17 (A_12 : Type) (F_13 : A_12 -> Linear) : Linear :=
| DFPair#18 (A_12 : Type)
              (F_13 : A_12 -> Linear)
                : (x_15 : A_12) -> ((F_13) x_15) -> (TFTensor#17 A_12 F_13).

Inductive TSN#19 (N_16 : TNat#2) : Type :=
| Dsn#20 (N_16 : TNat#2) : (n_18 : TNat#2) -> (TSN#19 N_16).

Definition bad_19 := (((Dsn#20 (DS#4 DO#3))) : (TSN#19 (DS#4 DO#3))).

Definition Loc_20 := ((TNat#2) : Type).

Axiom PtsTo_21 : Loc_20 -> Type -> Linear.

Definition Ptr_22 :=
  ((fun A_23 => (TFTensor#17 Loc_20 fun l_24 => ((PtsTo_21) l_24) A_23)) :
    (A_23 : Type) -> Linear).

Axiom New_25 : (A_27 : Type) -> A_27 -> (Ptr_22) A_27.

Axiom Free_28 : (A_30 : Type) -> (Ptr_22) A_30 -> TUnit#0.

Axiom Get_31 :
  (A_33 : Type) ->
    (l_35 : Loc_20) ->
      ((PtsTo_21) l_35) A_33 ->
        (TFTensor#17 A_33 fun __0 => ((PtsTo_21) l_35) A_33).

Axiom Set_36 :
  (A_38 : Type) ->
    (B_40 : Type) ->
      B_40 ->
        (l_42 : Loc_20) -> ((PtsTo_21) l_42) A_38 -> ((PtsTo_21) l_42) B_40.

Definition prev_43 :=
  ((fun n_44 x_45 =>
      match x_45 in (TSNat#8 n_44) return
        match n_44 with
        | (DO#3 ) => TUnit#0
        | (DS#4 n_44) => (TSNat#8 n_44)
        end
      with
      | (DZero#9 ) => Dtt#1
      | (DSucc#10 __0 x_45) => x_45
      end) :
    (n_44 : TNat#2) -> (x_45 : (TSNat#8 (DS#4 n_44))) -> (TSNat#8 n_44)).

Definition n_46 := ((((New_25) TNat#2) DO#3) : (Ptr_22) TNat#2).

Definition Assign_47 :=
  ((fun A_48 x_49 ptr_50 =>
      let (DFPair#18 l_51 c_52) := ptr_50 in
      let c_52 := (((((Set_36) A_48) A_48) x_49) l_51) c_52 in
      (DFPair#18 l_51 c_52)) :
    (A_48 : Type) ->
      (x_49 : A_48) -> (ptr_50 : (Ptr_22) A_48) -> (Ptr_22) A_48).

Definition main_53 :=
  ((let (DFPair#18 l_54 c_55) := n_46 in
    let (DFPair#18 x_56 c_55) := (((Get_31) TNat#2) l_54) c_55 in
    let __0 := ((Free_28) TNat#2) (DFPair#18 l_54 c_55) in x_56) : TNat#2).



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
| DSucc#10 : (n_93 : TNat#2) -> ((TSNat#8 n_93)) -> (TSNat#8 (DS#4 n_93)).

Inductive TEq#11 (A_95 : Type) : (A_95) -> (A_95) -> Type :=
| DRefl#12 (A_98 : Type) : (x_99 : A_98) -> (TEq#11 A_98 x_99 x_99).

Inductive TSigma#13 (A_100 : Type) (F_101 : A_100 -> Type) : Type :=
| DPair#14 (A_103 : Type)
             (F_104 : A_103 -> Type)
               : (x_106 : A_103) ->
                   ((F_104) x_106) -> (TSigma#13 A_103 F_104).

Inductive TTensor#15 (A_108 : Linear) (B_109 : Linear) : Linear :=
| DTPair#16 (A_110 : Linear)
              (B_111 : Linear)
                : (A_110) -> (B_111) -> (TTensor#15 A_110 B_111).

Inductive TFTensor#17 (A_114 : Type) (F_115 : A_114 -> Linear) : Linear :=
| DFPair#18 (A_117 : Type)
              (F_118 : A_117 -> Linear)
                : (x_120 : A_117) ->
                    ((F_118) x_120) -> (TFTensor#17 A_117 F_118).

Inductive TSN#19 (N_122 : TNat#2) : Type :=
| Dsn#20 (N_123 : TNat#2) : (n_124 : TNat#2) -> (TSN#19 N_123).

Definition bad_125 := (((Dsn#20 (DS#4 DO#3))) : (TSN#19 (DS#4 DO#3))).

Definition Loc_126 := ((TNat#2) : Type).

Axiom PtsTo_127 : Loc_126 -> Type -> Linear.

Definition Ptr_130 :=
  ((fun A_131 => (TFTensor#17 Loc_126 fun l_132 => ((PtsTo_127) l_132) A_131)) :
    (A_133 : Type) -> Linear).

Axiom New_134 : (A_135 : Type) -> A_135 -> (Ptr_130) A_135.

Axiom Free_137 : (A_138 : Type) -> (Ptr_130) A_138 -> TUnit#0.

Axiom Get_140 :
  (A_141 : Type) ->
    (l_142 : Loc_126) ->
      ((PtsTo_127) l_142) A_141 ->
        (TFTensor#17 A_141 fun __144 => ((PtsTo_127) l_142) A_141).

Axiom Set_145 :
  (A_146 : Type) ->
    (B_147 : Type) ->
      B_147 ->
        (l_149 : Loc_126) ->
          ((PtsTo_127) l_149) A_146 -> ((PtsTo_127) l_149) B_147.

Definition prev_151 :=
  ((fun n_152 x_153 =>
      match x_153 in (TSNat#8 n_155) return
        match n_155 with
        | (DO#3 ) => TUnit#0
        | (DS#4 n_156) => (TSNat#8 n_156)
        end
      with
      | (DZero#9 ) => Dtt#1
      | (DSucc#10 __157 x_158) => x_158
      end) :
    (n_159 : TNat#2) -> (x_160 : (TSNat#8 (DS#4 n_159))) -> (TSNat#8 n_159)).

Definition n_161 := ((((New_134) TNat#2) DO#3) : (Ptr_130) TNat#2).

Definition Assign_162 :=
  ((fun A_163 x_164 ptr_165 =>
      let x0_166 := ptr_165 in
      match x0_166 with
      | (DFPair#18 l_167 c_168) =>
        let c_169 := (((((Set_145) A_163) A_163) x_164) l_167) c_168 in
        (DFPair#18 l_167 c_169)
      end) :
    (A_170 : Type) ->
      (x_171 : A_170) -> (ptr_172 : (Ptr_130) A_170) -> (Ptr_130) A_170).

Definition main_173 :=
  ((let x_174 := n_161 in
    match x_174 with
    | (DFPair#18 l_175 c_176) =>
      let x_177 := (((Get_140) TNat#2) l_175) c_176 in
      match x_177 with
      | (DFPair#18 x_178 c_179) =>
        let __180 := ((Free_137) TNat#2) (DFPair#18 l_175 c_179) in x_178
      end
    end) : TNat#2).



v_ctx  := {
  main :0 (TNat#2)::w
  Assign :0
    ((A_775 : Type) ->
       (x_776 : A_775) ->
         (ptr_777 :
           (((fun A_778 =>
                (TFTensor#17
                  ((TNat#2) : Type) fun l_779 => ((DPtsTo#21) l_779) A_778)) :
              (A_780 : Type) -> Linear))
             A_775) ->
           (((fun A_781 =>
                (TFTensor#17
                  ((TNat#2) : Type) fun l_782 => ((DPtsTo#21) l_782) A_781)) :
              (A_783 : Type) -> Linear))
             A_775)::w
  n :1
    ((((fun A_784 =>
          (TFTensor#17
            ((TNat#2) : Type) fun l_785 => ((DPtsTo#21) l_785) A_784)) :
        (A_786 : Type) -> Linear))
       TNat#2)::1
  prev :0
    ((n_787 : TNat#2) -> (x_788 : (TSNat#8 (DS#4 n_787))) -> (TSNat#8 n_787))::w
  Set :0
    ((A_789 : Type) ->
       (B_790 : Type) ->
         B_790 ->
           (l_792 : ((TNat#2) : Type)) ->
             ((DPtsTo#21) l_792) A_789 -> ((DPtsTo#21) l_792) B_790)::w
  Get :0
    ((A_794 : Type) ->
       (l_795 : ((TNat#2) : Type)) ->
         ((DPtsTo#21) l_795) A_794 ->
           (TFTensor#17 A_794 fun __797 => ((DPtsTo#21) l_795) A_794))::w
  Free :0
    ((A_798 : Type) ->
       (((fun A_800 =>
            (TFTensor#17
              ((TNat#2) : Type) fun l_801 => ((DPtsTo#21) l_801) A_800)) :
          (A_802 : Type) -> Linear))
         A_798 -> TUnit#0)::w
  New :0
    ((A_803 : Type) ->
       A_803 ->
         (((fun A_805 =>
              (TFTensor#17
                ((TNat#2) : Type) fun l_806 => ((DPtsTo#21) l_806) A_805)) :
            (A_807 : Type) -> Linear))
           A_803)::w
  Ptr :0 ((A_808 : Type) -> Linear)::w
  PtsTo :0 (((TNat#2) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  bad :0 ((TSN#19 (DS#4 DO#3)))::w
}

match ((DNew#22) TNat#2) DO#3 with
| (DFPair#18 l_936 c_937) =>
  let x_938 := (((DGet#24) TNat#2) l_936) c_937 in
  match x_938 with
  | (DFPair#18 x_939 c_940) =>
    let __941 := ((DFree#23) TNat#2) (DFPair#18 l_936 c_940) in x_939
  end
end

