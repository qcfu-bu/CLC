Inductive TUnit#0 : Type :=
| Dtt#1 : TUnit#0.

Inductive TNat#2 : Type :=
| DO#3 : TNat#2
| DS#4 : (TNat#2) -> TNat#2.

Inductive TBool#5 : Type :=
| Dtrue#6 : TBool#5
| Dfalse#7 : TBool#5.

Inductive TEq#8 (A_1 : Type) : (A_1) -> (A_1) -> Type :=
| Drefl#9 (A_1 : Type) : (x_3 : A_1) -> (TEq#8 A_1 x_3 x_3).

Inductive TSigma#10 (A_4 : Type) (F_5 : A_4 -> Type) : Type :=
| Dpair#11 (A_4 : Type)
             (F_5 : A_4 -> Type)
               : (x_7 : A_4) -> ((F_5) x_7) -> (TSigma#10 A_4 F_5).

Inductive TTensor#12 (A_8 : Linear) (B_9 : Linear) : Linear :=
| Dtpair#13 (A_8 : Linear)
              (B_9 : Linear) : (A_8) -> (B_9) -> (TTensor#12 A_8 B_9).

Inductive TFTensor#14 (A_10 : Type) (F_11 : A_10 -> Linear) : Linear :=
| Dfpair#15 (A_10 : Type)
              (F_11 : A_10 -> Linear)
                : (x_13 : A_10) -> ((F_11) x_13) -> (TFTensor#14 A_10 F_11).

Definition Loc_14 := ((TNat#2) : Type).

Axiom PtsTo_15 : Loc_14 -> Type -> Linear.

Definition Ptr_16 :=
  ((fun A_17 => (TFTensor#14 Loc_14 fun l_18 => ((PtsTo_15) l_18) A_17)) :
    (A_17 : Type) -> Linear).

Axiom New_19 : (A_21 : Type) -> A_21 -> (Ptr_16) A_21.

Axiom Free_22 : (A_24 : Type) -> (Ptr_16) A_24 -> TUnit#0.

Axiom Get_25 :
  (A_27 : Type) ->
    (l_29 : Loc_14) ->
      ((PtsTo_15) l_29) A_27 ->
        (TFTensor#14 A_27 fun __0 => ((PtsTo_15) l_29) A_27).

Axiom Set_30 :
  (A_32 : Type) ->
    (B_34 : Type) ->
      B_34 ->
        (l_36 : Loc_14) -> ((PtsTo_15) l_36) A_32 -> ((PtsTo_15) l_36) B_34.

Definition lnId_37 := ((fun A_38 => A_38 >> A_38) : (A_38 : Type) -> Linear).

Inductive TLe#21 : (TNat#2) -> (TNat#2) -> Type :=
| DLtO#22 : (n_41 : TNat#2) -> (TLe#21 n_41 n_41)
| DLtS#23 : (m_46 : TNat#2) ->
              (n_47 : TNat#2) ->
                ((TLe#21 m_46 n_47)) -> (TLe#21 m_46 (DS#4 n_47)).

Definition add_48 :=
  ((fix add_48 m_49 n_50 =>
      match m_49 with
      | (DO#3 ) => n_50
      | (DS#4 m_49) => (DS#4 ((add_48) m_49) n_50)
      end) :
    (m_49 : TNat#2) -> (n_50 : TNat#2) -> TNat#2).

Inductive TArrVec#24 (A_51 : Type) (l_52 : Loc_14) : (TNat#2) -> Linear :=
| DNil#25 (A_51 : Type) (l_52 : Loc_14) : (TArrVec#24 A_51 l_52 DO#3)
| DCons#26 (A_51 : Type)
             (l_52 : Loc_14)
               : (n_55 : TNat#2) ->
                   (((PtsTo_15) ((add_48) l_52) n_55) A_51) ->
                     ((TArrVec#24 A_51 l_52 n_55)) ->
                       (TArrVec#24 A_51 l_52 (DS#4 n_55)).

Definition Lt_56 :=
  ((fun m_57 n_58 => (TLe#21 (DS#4 m_57) n_58)) :
    (m_57 : TNat#2) -> (n_58 : TNat#2) -> Type).

Definition Array_59 :=
  ((fun A_60 n_61 =>
      (TFTensor#14 Loc_14 fun l_62 => (TArrVec#24 A_60 l_62 n_61))) :
    (A_60 : Type) -> (n_61 : TNat#2) -> Linear).

Definition First_63 :=
  ((fun A_64 n_65 arr_66 =>
      let (Dfpair#15 l_68 v_69) := arr_66 in
      match v_69 in (TArrVec#24 __0 __0 n_65) return
        match n_65 with
        | (DO#3 ) => (lnId_37) A_64
        | (DS#4 n_65) =>
          (TFTensor#14 A_64 fun __0 => ((Array_59) A_64) (DS#4 n_65))
        end
      with
      | (DNil#25 ) => fun x_70 => x_70
      | (DCons#26 n_65 c_71 v_69) =>
        let (Dfpair#15 x_73 c_71) :=
          (((Get_25) A_64) ((add_48) l_68) n_65) c_71
        in (Dfpair#15 x_73 (Dfpair#15 l_68 (DCons#26 n_65 c_71 v_69)))
      end) :
    (A_64 : Type) ->
      (n_65 : TNat#2) ->
        (arr_66 : ((Array_59) A_64) (DS#4 n_65)) ->
          (TFTensor#14 A_64 fun __0 => ((Array_59) A_64) (DS#4 n_65))).

Definition main_74 := ((Dtt#1) : TUnit#0).



Inductive TUnit#0 : Type :=
| Dtt#1 : TUnit#0.

Inductive TNat#2 : Type :=
| DO#3 : TNat#2
| DS#4 : (TNat#2) -> TNat#2.

Inductive TBool#5 : Type :=
| Dtrue#6 : TBool#5
| Dfalse#7 : TBool#5.

Inductive TEq#8 (A_118 : Type) : (A_118) -> (A_118) -> Type :=
| Drefl#9 (A_121 : Type) : (x_122 : A_121) -> (TEq#8 A_121 x_122 x_122).

Inductive TSigma#10 (A_123 : Type) (F_124 : A_123 -> Type) : Type :=
| Dpair#11 (A_126 : Type)
             (F_127 : A_126 -> Type)
               : (x_129 : A_126) ->
                   ((F_127) x_129) -> (TSigma#10 A_126 F_127).

Inductive TTensor#12 (A_131 : Linear) (B_132 : Linear) : Linear :=
| Dtpair#13 (A_133 : Linear)
              (B_134 : Linear)
                : (A_133) -> (B_134) -> (TTensor#12 A_133 B_134).

Inductive TFTensor#14 (A_137 : Type) (F_138 : A_137 -> Linear) : Linear :=
| Dfpair#15 (A_140 : Type)
              (F_141 : A_140 -> Linear)
                : (x_143 : A_140) ->
                    ((F_141) x_143) -> (TFTensor#14 A_140 F_141).

Definition Loc_145 := ((TNat#2) : Type).

Axiom PtsTo_146 : Loc_145 -> Type -> Linear.

Definition Ptr_149 :=
  ((fun A_150 => (TFTensor#14 Loc_145 fun l_151 => ((PtsTo_146) l_151) A_150)) :
    (A_152 : Type) -> Linear).

Axiom New_153 : (A_154 : Type) -> A_154 -> (Ptr_149) A_154.

Axiom Free_156 : (A_157 : Type) -> (Ptr_149) A_157 -> TUnit#0.

Axiom Get_159 :
  (A_160 : Type) ->
    (l_161 : Loc_145) ->
      ((PtsTo_146) l_161) A_160 ->
        (TFTensor#14 A_160 fun __163 => ((PtsTo_146) l_161) A_160).

Axiom Set_164 :
  (A_165 : Type) ->
    (B_166 : Type) ->
      B_166 ->
        (l_168 : Loc_145) ->
          ((PtsTo_146) l_168) A_165 -> ((PtsTo_146) l_168) B_166.

Definition lnId_170 :=
  ((fun A_171 => A_171 >> A_171) : (A_173 : Type) -> Linear).

Inductive TLe#21 : (TNat#2) -> (TNat#2) -> Type :=
| DLtO#22 : (n_176 : TNat#2) -> (TLe#21 n_176 n_176)
| DLtS#23 : (m_177 : TNat#2) ->
              (n_178 : TNat#2) ->
                ((TLe#21 m_177 n_178)) -> (TLe#21 m_177 (DS#4 n_178)).

Definition add_180 :=
  ((fix add_181 m_182 n_183 =>
      match m_182 with
      | (DO#3 ) => n_183
      | (DS#4 m_184) => (DS#4 ((add_181) m_184) n_183)
      end) :
    (m_185 : TNat#2) -> (n_186 : TNat#2) -> TNat#2).

Inductive TArrVec#24 (A_187 : Type) (l_188 : Loc_145) : (TNat#2) -> Linear :=
| DNil#25 (A_190 : Type) (l_191 : Loc_145) : (TArrVec#24 A_190 l_191 DO#3)
| DCons#26 (A_192 : Type)
             (l_193 : Loc_145)
               : (n_194 : TNat#2) ->
                   (((PtsTo_146) ((add_180) l_193) n_194) A_192) ->
                     ((TArrVec#24 A_192 l_193 n_194)) ->
                       (TArrVec#24 A_192 l_193 (DS#4 n_194)).

Definition Lt_197 :=
  ((fun m_198 n_199 => (TLe#21 (DS#4 m_198) n_199)) :
    (m_200 : TNat#2) -> (n_201 : TNat#2) -> Type).

Definition Array_202 :=
  ((fun A_203 n_204 =>
      (TFTensor#14 Loc_145 fun l_205 => (TArrVec#24 A_203 l_205 n_204))) :
    (A_206 : Type) -> (n_207 : TNat#2) -> Linear).

Definition First_208 :=
  ((fun A_209 n_210 arr_211 =>
      let x_212 := arr_211 in
      match x_212 with
      | (Dfpair#15 l_213 v_214) =>
        match v_214 in (TArrVec#24 __216 __217 n_218) return
          match n_218 with
          | (DO#3 ) => (lnId_170) A_209
          | (DS#4 n_219) =>
            (TFTensor#14 A_209 fun __220 => ((Array_202) A_209) (DS#4 n_219))
          end
        with
        | (DNil#25 ) => fun x_221 => x_221
        | (DCons#26 n_222 c_223 v_224) =>
          let x_225 := (((Get_159) A_209) ((add_180) l_213) n_222) c_223 in
          match x_225 with
          | (Dfpair#15 x_226 c_227) =>
            (Dfpair#15 x_226 (Dfpair#15 l_213 (DCons#26 n_222 c_227 v_224)))
          end
        end
      end) :
    (A_228 : Type) ->
      (n_229 : TNat#2) ->
        (arr_230 : ((Array_202) A_228) (DS#4 n_229)) ->
          (TFTensor#14 A_228 fun __231 => ((Array_202) A_228) (DS#4 n_229))).

Definition main_232 := ((Dtt#1) : TUnit#0).



v_ctx  := {
  main :0 (TUnit#0)::w
  First :0
    ((A_1808 : Type) ->
       (n_1809 : TNat#2) ->
         (arr_1810 :
           ((((fun A_1811 n_1812 =>
                 (TFTensor#14
                   ((TNat#2) : Type)
                     fun l_1813 => (TArrVec#24 A_1811 l_1813 n_1812))) :
               (A_1814 : Type) -> (n_1815 : TNat#2) -> Linear))
              A_1808)
             (DS#4 n_1809)) ->
           (TFTensor#14
             A_1808
               fun __1816 =>
                 ((((fun A_1817 n_1818 =>
                       (TFTensor#14
                         ((TNat#2) : Type)
                           fun l_1819 => (TArrVec#24 A_1817 l_1819 n_1818))) :
                     (A_1820 : Type) -> (n_1821 : TNat#2) -> Linear))
                    A_1808)
                   (DS#4 n_1809)))::w
  Array :0 ((A_1822 : Type) -> (n_1823 : TNat#2) -> Linear)::w
  Lt :0 ((m_1824 : TNat#2) -> (n_1825 : TNat#2) -> Type)::w
  add :0 ((m_1826 : TNat#2) -> (n_1827 : TNat#2) -> TNat#2)::w
  lnId :0 ((A_1828 : Type) -> Linear)::w
  Set :0
    ((A_1829 : Type) ->
       (B_1830 : Type) ->
         B_1830 ->
           (l_1832 : ((TNat#2) : Type)) ->
             ((DPtsTo#16) l_1832) A_1829 -> ((DPtsTo#16) l_1832) B_1830)::w
  Get :0
    ((A_1834 : Type) ->
       (l_1835 : ((TNat#2) : Type)) ->
         ((DPtsTo#16) l_1835) A_1834 ->
           (TFTensor#14 A_1834 fun __1837 => ((DPtsTo#16) l_1835) A_1834))::w
  Free :0
    ((A_1838 : Type) ->
       (((fun A_1840 =>
            (TFTensor#14
              ((TNat#2) : Type) fun l_1841 => ((DPtsTo#16) l_1841) A_1840)) :
          (A_1842 : Type) -> Linear))
         A_1838 -> TUnit#0)::w
  New :0
    ((A_1843 : Type) ->
       A_1843 ->
         (((fun A_1845 =>
              (TFTensor#14
                ((TNat#2) : Type) fun l_1846 => ((DPtsTo#16) l_1846) A_1845)) :
            (A_1847 : Type) -> Linear))
           A_1843)::w
  Ptr :0 ((A_1848 : Type) -> Linear)::w
  PtsTo :0 (((TNat#2) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
}

Dtt#1

