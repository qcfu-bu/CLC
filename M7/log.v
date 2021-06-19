Inductive TEq#0 (A_1 : Type) (x_2 : A_1) : (A_1) -> Type :=
| Drefl#1 (A_1 : Type) (x_2 : A_1) : (TEq#0 A_1 x_2 x_2).

Definition eq_sym_3 :=
  ((fun A_4 x_5 y_6 e_7 =>
      match e_7 in (TEq#0 __0 __0 y_6) return (TEq#0 A_4 y_6 x_5) with
      | (Drefl#1 ) => Drefl#1
      end) :
    (A_4 : Type) ->
      (x_5 : A_4) ->
        (y_6 : A_4) -> (e_7 : (TEq#0 A_4 x_5 y_6)) -> (TEq#0 A_4 y_6 x_5)).

Definition TyInd_8 :=
  ((fun A_9 x_10 y_11 P_12 e_13 f_14 =>
      match e_13 in (TEq#0 __0 __0 y_11) return (P_12) y_11 with
      | (Drefl#1 ) => f_14
      end) :
    (A_9 : Type) ->
      (x_10 : A_9) ->
        (y_11 : A_9) ->
          (P_12 : A_9 -> Type) ->
            (e_13 : (TEq#0 A_9 x_10 y_11)) ->
              (f_14 : (P_12) x_10) -> (P_12) y_11).

Definition LnInd_15 :=
  ((fun A_16 x_17 y_18 P_19 e_20 f_21 =>
      match e_20 in (TEq#0 __0 __0 y_18) return (P_19) y_18 with
      | (Drefl#1 ) => f_21
      end) :
    (A_16 : Type) ->
      (x_17 : A_16) ->
        (y_18 : A_16) ->
          (P_19 : A_16 -> Linear) ->
            (e_20 : (TEq#0 A_16 x_17 y_18)) ->
              (f_21 : (P_19) x_17) -> (P_19) y_18).

Inductive TUnit#2 : Type :=
| Dtt#3 : TUnit#2.

Inductive TNat#4 : Type :=
| DO#5 : TNat#4
| DS#6 : (TNat#4) -> TNat#4.

Inductive TBool#7 : Type :=
| Dtrue#8 : TBool#7
| Dfalse#9 : TBool#7.

Inductive TSigma#10 (A_22 : Type) (F_23 : A_22 -> Type) : Type :=
| Dpair#11 (A_22 : Type)
             (F_23 : A_22 -> Type)
               : (x_25 : A_22) -> ((F_23) x_25) -> (TSigma#10 A_22 F_23).

Inductive TTensor#12 (A_26 : Linear) (B_27 : Linear) : Linear :=
| Dtpair#13 (A_26 : Linear)
              (B_27 : Linear) : (A_26) -> (B_27) -> (TTensor#12 A_26 B_27).

Inductive TFTensor#14 (A_28 : Type) (F_29 : A_28 -> Linear) : Linear :=
| Dfpair#15 (A_28 : Type)
              (F_29 : A_28 -> Linear)
                : (x_31 : A_28) -> ((F_29) x_31) -> (TFTensor#14 A_28 F_29).

Definition Loc_32 := ((TNat#4) : Type).

Axiom PtsTo_33 : Loc_32 -> Type -> Linear.

Definition Ptr_34 :=
  ((fun A_35 => (TFTensor#14 Loc_32 fun l_36 => ((PtsTo_33) l_36) A_35)) :
    (A_35 : Type) -> Linear).

Axiom New_37 : (A_39 : Type) -> A_39 -> (Ptr_34) A_39.

Axiom Free_40 : (A_42 : Type) -> (Ptr_34) A_42 -> TUnit#2.

Axiom Get_43 :
  (A_45 : Type) ->
    (l_47 : Loc_32) ->
      ((PtsTo_33) l_47) A_45 ->
        (TFTensor#14 A_45 fun __0 => ((PtsTo_33) l_47) A_45).

Axiom Set_48 :
  (A_50 : Type) ->
    (B_52 : Type) ->
      B_52 ->
        (l_54 : Loc_32) -> ((PtsTo_33) l_54) A_50 -> ((PtsTo_33) l_54) B_52.

Definition lnId_55 := ((fun A_56 => A_56 >> A_56) : (A_56 : Type) -> Linear).

Definition add_57 :=
  ((fix add_57 m_58 n_59 =>
      match m_58 with
      | (DO#5 ) => n_59
      | (DS#6 m_58) => (DS#6 ((add_57) m_58) n_59)
      end) :
    (m_58 : TNat#4) -> (n_59 : TNat#4) -> TNat#4).

Inductive TFin#21 : (TNat#4) -> Type :=
| DF1#22 : (n_63 : TNat#4) -> (TFin#21 (DS#6 n_63))
| DFS#23 : (n_68 : TNat#4) -> ((TFin#21 n_68)) -> (TFin#21 (DS#6 n_68)).

Inductive TArrVec#24 (A_70 : Type) (l_71 : Loc_32) : (TNat#4) -> Linear :=
| DNil#25 (A_70 : Type) (l_71 : Loc_32) : (TArrVec#24 A_70 l_71 DO#5)
| DCons#26 (A_70 : Type)
             (l_71 : Loc_32)
               : (n_75 : TNat#4) ->
                   (((PtsTo_33) ((add_57) l_71) n_75) A_70) ->
                     ((TArrVec#24 A_70 l_71 n_75)) ->
                       (TArrVec#24 A_70 l_71 (DS#6 n_75)).

Definition Array_77 :=
  ((fun A_78 n_79 =>
      (TFTensor#14 Loc_32 fun l_80 => (TArrVec#24 A_78 l_80 n_79))) :
    (A_78 : Type) -> (n_79 : TNat#4) -> Linear).

Definition main_81 := ((Dtt#3) : TUnit#2).



Inductive TEq#0 (A_135 : Type) (x_136 : A_135) : (A_135) -> Type :=
| Drefl#1 (A_138 : Type) (x_139 : A_138) : (TEq#0 A_138 x_139 x_139).

Definition eq_sym_140 :=
  ((fun A_141 x_142 y_143 e_144 =>
      match e_144 in (TEq#0 __146 __147 y_148) return
        (TEq#0 A_141 y_148 x_142)
      with
      | (Drefl#1 ) => Drefl#1
      end) :
    (A_149 : Type) ->
      (x_150 : A_149) ->
        (y_151 : A_149) ->
          (e_152 : (TEq#0 A_149 x_150 y_151)) -> (TEq#0 A_149 y_151 x_150)).

Definition TyInd_153 :=
  ((fun A_154 x_155 y_156 P_157 e_158 f_159 =>
      match e_158 in (TEq#0 __161 __162 y_163) return (P_157) y_163 with
      | (Drefl#1 ) => f_159
      end) :
    (A_164 : Type) ->
      (x_165 : A_164) ->
        (y_166 : A_164) ->
          (P_167 : A_164 -> Type) ->
            (e_169 : (TEq#0 A_164 x_165 y_166)) ->
              (f_170 : (P_167) x_165) -> (P_167) y_166).

Definition LnInd_171 :=
  ((fun A_172 x_173 y_174 P_175 e_176 f_177 =>
      match e_176 in (TEq#0 __179 __180 y_181) return (P_175) y_181 with
      | (Drefl#1 ) => f_177
      end) :
    (A_182 : Type) ->
      (x_183 : A_182) ->
        (y_184 : A_182) ->
          (P_185 : A_182 -> Linear) ->
            (e_187 : (TEq#0 A_182 x_183 y_184)) ->
              (f_188 : (P_185) x_183) -> (P_185) y_184).

Inductive TUnit#2 : Type :=
| Dtt#3 : TUnit#2.

Inductive TNat#4 : Type :=
| DO#5 : TNat#4
| DS#6 : (TNat#4) -> TNat#4.

Inductive TBool#7 : Type :=
| Dtrue#8 : TBool#7
| Dfalse#9 : TBool#7.

Inductive TSigma#10 (A_190 : Type) (F_191 : A_190 -> Type) : Type :=
| Dpair#11 (A_193 : Type)
             (F_194 : A_193 -> Type)
               : (x_196 : A_193) ->
                   ((F_194) x_196) -> (TSigma#10 A_193 F_194).

Inductive TTensor#12 (A_198 : Linear) (B_199 : Linear) : Linear :=
| Dtpair#13 (A_200 : Linear)
              (B_201 : Linear)
                : (A_200) -> (B_201) -> (TTensor#12 A_200 B_201).

Inductive TFTensor#14 (A_204 : Type) (F_205 : A_204 -> Linear) : Linear :=
| Dfpair#15 (A_207 : Type)
              (F_208 : A_207 -> Linear)
                : (x_210 : A_207) ->
                    ((F_208) x_210) -> (TFTensor#14 A_207 F_208).

Definition Loc_212 := ((TNat#4) : Type).

Axiom PtsTo_213 : Loc_212 -> Type -> Linear.

Definition Ptr_216 :=
  ((fun A_217 => (TFTensor#14 Loc_212 fun l_218 => ((PtsTo_213) l_218) A_217)) :
    (A_219 : Type) -> Linear).

Axiom New_220 : (A_221 : Type) -> A_221 -> (Ptr_216) A_221.

Axiom Free_223 : (A_224 : Type) -> (Ptr_216) A_224 -> TUnit#2.

Axiom Get_226 :
  (A_227 : Type) ->
    (l_228 : Loc_212) ->
      ((PtsTo_213) l_228) A_227 ->
        (TFTensor#14 A_227 fun __230 => ((PtsTo_213) l_228) A_227).

Axiom Set_231 :
  (A_232 : Type) ->
    (B_233 : Type) ->
      B_233 ->
        (l_235 : Loc_212) ->
          ((PtsTo_213) l_235) A_232 -> ((PtsTo_213) l_235) B_233.

Definition lnId_237 :=
  ((fun A_238 => A_238 >> A_238) : (A_240 : Type) -> Linear).

Definition add_241 :=
  ((fix add_242 m_243 n_244 =>
      match m_243 with
      | (DO#5 ) => n_244
      | (DS#6 m_245) => (DS#6 ((add_242) m_245) n_244)
      end) :
    (m_246 : TNat#4) -> (n_247 : TNat#4) -> TNat#4).

Inductive TFin#21 : (TNat#4) -> Type :=
| DF1#22 : (n_249 : TNat#4) -> (TFin#21 (DS#6 n_249))
| DFS#23 : (n_250 : TNat#4) -> ((TFin#21 n_250)) -> (TFin#21 (DS#6 n_250)).

Inductive TArrVec#24 (A_252 : Type) (l_253 : Loc_212) : (TNat#4) -> Linear :=
| DNil#25 (A_255 : Type) (l_256 : Loc_212) : (TArrVec#24 A_255 l_256 DO#5)
| DCons#26 (A_257 : Type)
             (l_258 : Loc_212)
               : (n_259 : TNat#4) ->
                   (((PtsTo_213) ((add_241) l_258) n_259) A_257) ->
                     ((TArrVec#24 A_257 l_258 n_259)) ->
                       (TArrVec#24 A_257 l_258 (DS#6 n_259)).

Definition Array_262 :=
  ((fun A_263 n_264 =>
      (TFTensor#14 Loc_212 fun l_265 => (TArrVec#24 A_263 l_265 n_264))) :
    (A_266 : Type) -> (n_267 : TNat#4) -> Linear).

Definition main_268 := ((Dtt#3) : TUnit#2).



v_ctx  := {
  main :0 (TUnit#2)::w
  Array :0 ((A_748 : Type) -> (n_749 : TNat#4) -> Linear)::w
  add :0 ((m_750 : TNat#4) -> (n_751 : TNat#4) -> TNat#4)::w
  lnId :0 ((A_752 : Type) -> Linear)::w
  Set :0
    ((A_753 : Type) ->
       (B_754 : Type) ->
         B_754 ->
           (l_756 : ((TNat#4) : Type)) ->
             ((DPtsTo#16) l_756) A_753 -> ((DPtsTo#16) l_756) B_754)::w
  Get :0
    ((A_758 : Type) ->
       (l_759 : ((TNat#4) : Type)) ->
         ((DPtsTo#16) l_759) A_758 ->
           (TFTensor#14 A_758 fun __761 => ((DPtsTo#16) l_759) A_758))::w
  Free :0
    ((A_762 : Type) ->
       (((fun A_764 =>
            (TFTensor#14
              ((TNat#4) : Type) fun l_765 => ((DPtsTo#16) l_765) A_764)) :
          (A_766 : Type) -> Linear))
         A_762 -> TUnit#2)::w
  New :0
    ((A_767 : Type) ->
       A_767 ->
         (((fun A_769 =>
              (TFTensor#14
                ((TNat#4) : Type) fun l_770 => ((DPtsTo#16) l_770) A_769)) :
            (A_771 : Type) -> Linear))
           A_767)::w
  Ptr :0 ((A_772 : Type) -> Linear)::w
  PtsTo :0 (((TNat#4) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  LnInd :0
    ((A_775 : Type) ->
       (x_776 : A_775) ->
         (y_777 : A_775) ->
           (P_778 : A_775 -> Linear) ->
             (e_780 : (TEq#0 A_775 x_776 y_777)) ->
               (f_781 : (P_778) x_776) -> (P_778) y_777)::w
  TyInd :0
    ((A_782 : Type) ->
       (x_783 : A_782) ->
         (y_784 : A_782) ->
           (P_785 : A_782 -> Type) ->
             (e_787 : (TEq#0 A_782 x_783 y_784)) ->
               (f_788 : (P_785) x_783) -> (P_785) y_784)::w
  eq_sym :0
    ((A_789 : Type) ->
       (x_790 : A_789) ->
         (y_791 : A_789) ->
           (e_792 : (TEq#0 A_789 x_790 y_791)) -> (TEq#0 A_789 y_791 x_790))::w
}

Dtt#3

