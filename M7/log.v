Inductive TEq#0 (A_1 : Type) (x_2 : A_1) : (A_1) -> Type :=
| Drefl#1 (A_1 : Type) (x_2 : A_1) : (TEq#0 A_1 x_2 x_2).

Definition Eq_sym_3 :=
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

Inductive TOne#4 : Linear :=
| Dll#5 : TOne#4.

Inductive TNat#6 : Type :=
| DO#7 : TNat#6
| DS#8 : (TNat#6) -> TNat#6.

Inductive TBool#9 : Type :=
| Dtrue#10 : TBool#9
| Dfalse#11 : TBool#9.

Inductive TSigma#12 (A_22 : Type) (F_23 : A_22 -> Type) : Type :=
| Dpair#13 (A_22 : Type)
             (F_23 : A_22 -> Type)
               : (x_25 : A_22) -> ((F_23) x_25) -> (TSigma#12 A_22 F_23).

Inductive TTensor#14 (A_26 : Linear) (B_27 : Linear) : Linear :=
| Dtpair#15 (A_26 : Linear)
              (B_27 : Linear) : (A_26) -> (B_27) -> (TTensor#14 A_26 B_27).

Inductive TFTensor#16 (A_28 : Type) (F_29 : A_28 -> Linear) : Linear :=
| Dfpair#17 (A_28 : Type)
              (F_29 : A_28 -> Linear)
                : (x_31 : A_28) -> ((F_29) x_31) -> (TFTensor#16 A_28 F_29).

Definition Loc_32 := ((TNat#6) : Type).

Axiom PtsTo_33 : Loc_32 -> Type -> Linear.

Definition Ptr_34 :=
  ((fun A_35 => (TFTensor#16 Loc_32 fun l_36 => ((PtsTo_33) l_36) A_35)) :
    (A_35 : Type) -> Linear).

Axiom New_37 : (A_39 : Type) -> A_39 -> (Ptr_34) A_39.

Axiom Free_40 : (A_42 : Type) -> (Ptr_34) A_42 -> TUnit#2.

Axiom Get_43 :
  (A_45 : Type) ->
    (l_47 : Loc_32) ->
      ((PtsTo_33) l_47) A_45 ->
        (TFTensor#16 A_45 fun __0 => ((PtsTo_33) l_47) A_45).

Axiom Set_48 :
  (A_50 : Type) ->
    (B_52 : Type) ->
      B_52 ->
        (l_54 : Loc_32) -> ((PtsTo_33) l_54) A_50 -> ((PtsTo_33) l_54) B_52.

Inductive TFin#23 : (TNat#6) -> Type :=
| DF1#24 : (n_58 : TNat#6) -> (TFin#23 (DS#8 n_58))
| DFS#25 : (n_63 : TNat#6) -> ((TFin#23 n_63)) -> (TFin#23 (DS#8 n_63)).

Inductive TVec#26 (A_65 : Type) : (TNat#6) -> Type :=
| DNil#27 (A_65 : Type) : (TVec#26 A_65 DO#7)
| DCons#28 (A_65 : Type)
             : (n_69 : TNat#6) ->
                 (A_65) ->
                   ((TVec#26 A_65 n_69)) -> (TVec#26 A_65 (DS#8 n_69)).

Definition nth_71 :=
  ((fix nth_71 A_72 n_73 x_74 v_75 =>
      (match x_74 in (TFin#23 n_73) return (TVec#26 A_72 n_73) -> A_72 with
       | (DF1#24 n_73) =>
         fun v_75 =>
           match v_75 in (TVec#26 __0 n_73) return
             match n_73 with
             | (DO#7 ) => TUnit#2
             | (DS#8 __0) => A_72
             end
           with
           | (DNil#27 ) => Dtt#3
           | (DCons#28 __0 x_74 __0) => x_74
           end
       | (DFS#25 n_73 x_74) =>
         fun v_75 =>
           (match v_75 in (TVec#26 __0 n_73) return
              match n_73 with
              | (DO#7 ) => TUnit#2
              | (DS#8 n_73) => (TFin#23 n_73) -> A_72
              end
            with
            | (DNil#27 ) => Dtt#3
            | (DCons#28 n_73 __0 v_75) =>
              fun x_74 => ((((nth_71) A_72) n_73) x_74) v_75
            end) x_74
       end) v_75) :
    (A_72 : Type) ->
      (n_73 : TNat#6) ->
        (x_74 : (TFin#23 n_73)) -> (v_75 : (TVec#26 A_72 n_73)) -> A_72).

Definition main_76 := ((Dtt#3) : TUnit#2).



Inductive TEq#0 (A_149 : Type) (x_150 : A_149) : (A_149) -> Type :=
| Drefl#1 (A_152 : Type) (x_153 : A_152) : (TEq#0 A_152 x_153 x_153).

Definition Eq_sym_154 :=
  ((fun A_155 x_156 y_157 e_158 =>
      match e_158 in (TEq#0 __160 __161 y_162) return
        (TEq#0 A_155 y_162 x_156)
      with
      | (Drefl#1 ) => Drefl#1
      end) :
    (A_163 : Type) ->
      (x_164 : A_163) ->
        (y_165 : A_163) ->
          (e_166 : (TEq#0 A_163 x_164 y_165)) -> (TEq#0 A_163 y_165 x_164)).

Definition TyInd_167 :=
  ((fun A_168 x_169 y_170 P_171 e_172 f_173 =>
      match e_172 in (TEq#0 __175 __176 y_177) return (P_171) y_177 with
      | (Drefl#1 ) => f_173
      end) :
    (A_178 : Type) ->
      (x_179 : A_178) ->
        (y_180 : A_178) ->
          (P_181 : A_178 -> Type) ->
            (e_183 : (TEq#0 A_178 x_179 y_180)) ->
              (f_184 : (P_181) x_179) -> (P_181) y_180).

Definition LnInd_185 :=
  ((fun A_186 x_187 y_188 P_189 e_190 f_191 =>
      match e_190 in (TEq#0 __193 __194 y_195) return (P_189) y_195 with
      | (Drefl#1 ) => f_191
      end) :
    (A_196 : Type) ->
      (x_197 : A_196) ->
        (y_198 : A_196) ->
          (P_199 : A_196 -> Linear) ->
            (e_201 : (TEq#0 A_196 x_197 y_198)) ->
              (f_202 : (P_199) x_197) -> (P_199) y_198).

Inductive TUnit#2 : Type :=
| Dtt#3 : TUnit#2.

Inductive TOne#4 : Linear :=
| Dll#5 : TOne#4.

Inductive TNat#6 : Type :=
| DO#7 : TNat#6
| DS#8 : (TNat#6) -> TNat#6.

Inductive TBool#9 : Type :=
| Dtrue#10 : TBool#9
| Dfalse#11 : TBool#9.

Inductive TSigma#12 (A_204 : Type) (F_205 : A_204 -> Type) : Type :=
| Dpair#13 (A_207 : Type)
             (F_208 : A_207 -> Type)
               : (x_210 : A_207) ->
                   ((F_208) x_210) -> (TSigma#12 A_207 F_208).

Inductive TTensor#14 (A_212 : Linear) (B_213 : Linear) : Linear :=
| Dtpair#15 (A_214 : Linear)
              (B_215 : Linear)
                : (A_214) -> (B_215) -> (TTensor#14 A_214 B_215).

Inductive TFTensor#16 (A_218 : Type) (F_219 : A_218 -> Linear) : Linear :=
| Dfpair#17 (A_221 : Type)
              (F_222 : A_221 -> Linear)
                : (x_224 : A_221) ->
                    ((F_222) x_224) -> (TFTensor#16 A_221 F_222).

Definition Loc_226 := ((TNat#6) : Type).

Axiom PtsTo_227 : Loc_226 -> Type -> Linear.

Definition Ptr_230 :=
  ((fun A_231 => (TFTensor#16 Loc_226 fun l_232 => ((PtsTo_227) l_232) A_231)) :
    (A_233 : Type) -> Linear).

Axiom New_234 : (A_235 : Type) -> A_235 -> (Ptr_230) A_235.

Axiom Free_237 : (A_238 : Type) -> (Ptr_230) A_238 -> TUnit#2.

Axiom Get_240 :
  (A_241 : Type) ->
    (l_242 : Loc_226) ->
      ((PtsTo_227) l_242) A_241 ->
        (TFTensor#16 A_241 fun __244 => ((PtsTo_227) l_242) A_241).

Axiom Set_245 :
  (A_246 : Type) ->
    (B_247 : Type) ->
      B_247 ->
        (l_249 : Loc_226) ->
          ((PtsTo_227) l_249) A_246 -> ((PtsTo_227) l_249) B_247.

Inductive TFin#23 : (TNat#6) -> Type :=
| DF1#24 : (n_252 : TNat#6) -> (TFin#23 (DS#8 n_252))
| DFS#25 : (n_253 : TNat#6) -> ((TFin#23 n_253)) -> (TFin#23 (DS#8 n_253)).

Inductive TVec#26 (A_255 : Type) : (TNat#6) -> Type :=
| DNil#27 (A_257 : Type) : (TVec#26 A_257 DO#7)
| DCons#28 (A_258 : Type)
             : (n_259 : TNat#6) ->
                 (A_258) ->
                   ((TVec#26 A_258 n_259)) -> (TVec#26 A_258 (DS#8 n_259)).

Definition nth_262 :=
  ((fix nth_263 A_264 n_265 x_266 v_267 =>
      (match x_266 in (TFin#23 n_269) return (TVec#26 A_264 n_269) -> A_264
       with
       | (DF1#24 n_271) =>
         fun v_272 =>
           match v_272 in (TVec#26 __274 n_275) return
             match n_275 with
             | (DO#7 ) => TUnit#2
             | (DS#8 __276) => A_264
             end
           with
           | (DNil#27 ) => Dtt#3
           | (DCons#28 __277 x_278 __279) => x_278
           end
       | (DFS#25 n_280 x_281) =>
         fun v_282 =>
           (match v_282 in (TVec#26 __284 n_285) return
              match n_285 with
              | (DO#7 ) => TUnit#2
              | (DS#8 n_286) => (TFin#23 n_286) -> A_264
              end
            with
            | (DNil#27 ) => Dtt#3
            | (DCons#28 n_288 __289 v_290) =>
              fun x_291 => ((((nth_263) A_264) n_288) x_291) v_290
            end) x_281
       end) v_267) :
    (A_292 : Type) ->
      (n_293 : TNat#6) ->
        (x_294 : (TFin#23 n_293)) -> (v_295 : (TVec#26 A_292 n_293)) -> A_292).

Definition main_296 := ((Dtt#3) : TUnit#2).



v_ctx  := {
  main :0 (TUnit#2)::w
  nth :0
    ((A_954 : Type) ->
       (n_955 : TNat#6) ->
         (x_956 : (TFin#23 n_955)) ->
           (v_957 : (TVec#26 A_954 n_955)) -> A_954)::w
  Set :0
    ((A_958 : Type) ->
       (B_959 : Type) ->
         B_959 ->
           (l_961 : ((TNat#6) : Type)) ->
             ((DPtsTo#18) l_961) A_958 -> ((DPtsTo#18) l_961) B_959)::w
  Get :0
    ((A_963 : Type) ->
       (l_964 : ((TNat#6) : Type)) ->
         ((DPtsTo#18) l_964) A_963 ->
           (TFTensor#16 A_963 fun __966 => ((DPtsTo#18) l_964) A_963))::w
  Free :0
    ((A_967 : Type) ->
       (((fun A_969 =>
            (TFTensor#16
              ((TNat#6) : Type) fun l_970 => ((DPtsTo#18) l_970) A_969)) :
          (A_971 : Type) -> Linear))
         A_967 -> TUnit#2)::w
  New :0
    ((A_972 : Type) ->
       A_972 ->
         (((fun A_974 =>
              (TFTensor#16
                ((TNat#6) : Type) fun l_975 => ((DPtsTo#18) l_975) A_974)) :
            (A_976 : Type) -> Linear))
           A_972)::w
  Ptr :0 ((A_977 : Type) -> Linear)::w
  PtsTo :0 (((TNat#6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  LnInd :0
    ((A_980 : Type) ->
       (x_981 : A_980) ->
         (y_982 : A_980) ->
           (P_983 : A_980 -> Linear) ->
             (e_985 : (TEq#0 A_980 x_981 y_982)) ->
               (f_986 : (P_983) x_981) -> (P_983) y_982)::w
  TyInd :0
    ((A_987 : Type) ->
       (x_988 : A_987) ->
         (y_989 : A_987) ->
           (P_990 : A_987 -> Type) ->
             (e_992 : (TEq#0 A_987 x_988 y_989)) ->
               (f_993 : (P_990) x_988) -> (P_990) y_989)::w
  Eq_sym :0
    ((A_994 : Type) ->
       (x_995 : A_994) ->
         (y_996 : A_994) ->
           (e_997 : (TEq#0 A_994 x_995 y_996)) -> (TEq#0 A_994 y_996 x_995))::w
}

Dtt#3

