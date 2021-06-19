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

Definition First_81 :=
  ((fun A_82 n_83 arr_84 =>
      let (Dfpair#15 l_88 v_89) := arr_84 in
      (match v_89 in (TArrVec#24 __0 __0 n1_90) return
         match n1_90 with
         | (DO#5 ) => (TEq#0 TNat#4 n_83 n_83) >> (lnId_55) A_82
         | (DS#6 n2_91) =>
           (TEq#0 TNat#4 n2_91 n_83) >>
             (TFTensor#14 A_82 fun __0 => ((Array_77) A_82) (DS#6 n_83))
         end
       with
       | (DNil#25 ) => fun __0 x_93 => x_93
       | (DCons#26 n1_90 c_94 v_89) =>
         fun pf_95 =>
           let f1_96 :=
             ((fun n_83 => ((PtsTo_33) ((add_57) l_88) n_83) A_82) :
               TNat#4 -> Linear)
           in
           let f2_97 :=
             ((fun n_83 => (TArrVec#24 A_82 l_88 n_83)) : TNat#4 -> Linear)
           in
           let c_94 :=
             ((((((LnInd_15) TNat#4) n1_90) n_83) f1_96) pf_95) c_94
           in
           let v_89 :=
             ((((((LnInd_15) TNat#4) n1_90) n_83) f2_97) pf_95) v_89
           in
           let (Dfpair#15 x_99 c_94) :=
             (((Get_43) A_82) ((add_57) l_88) n_83) c_94
           in (Dfpair#15 x_99 (Dfpair#15 l_88 (DCons#26 n_83 c_94 v_89)))
       end) Drefl#1) :
    (A_82 : Type) ->
      (n_83 : TNat#4) ->
        (arr_84 : ((Array_77) A_82) (DS#6 n_83)) ->
          (TFTensor#14 A_82 fun __0 => ((Array_77) A_82) (DS#6 n_83))).

Definition main_100 := ((Dtt#3) : TUnit#2).



Inductive TEq#0 (A_171 : Type) (x_172 : A_171) : (A_171) -> Type :=
| Drefl#1 (A_174 : Type) (x_175 : A_174) : (TEq#0 A_174 x_175 x_175).

Definition Eq_sym_176 :=
  ((fun A_177 x_178 y_179 e_180 =>
      match e_180 in (TEq#0 __182 __183 y_184) return
        (TEq#0 A_177 y_184 x_178)
      with
      | (Drefl#1 ) => Drefl#1
      end) :
    (A_185 : Type) ->
      (x_186 : A_185) ->
        (y_187 : A_185) ->
          (e_188 : (TEq#0 A_185 x_186 y_187)) -> (TEq#0 A_185 y_187 x_186)).

Definition TyInd_189 :=
  ((fun A_190 x_191 y_192 P_193 e_194 f_195 =>
      match e_194 in (TEq#0 __197 __198 y_199) return (P_193) y_199 with
      | (Drefl#1 ) => f_195
      end) :
    (A_200 : Type) ->
      (x_201 : A_200) ->
        (y_202 : A_200) ->
          (P_203 : A_200 -> Type) ->
            (e_205 : (TEq#0 A_200 x_201 y_202)) ->
              (f_206 : (P_203) x_201) -> (P_203) y_202).

Definition LnInd_207 :=
  ((fun A_208 x_209 y_210 P_211 e_212 f_213 =>
      match e_212 in (TEq#0 __215 __216 y_217) return (P_211) y_217 with
      | (Drefl#1 ) => f_213
      end) :
    (A_218 : Type) ->
      (x_219 : A_218) ->
        (y_220 : A_218) ->
          (P_221 : A_218 -> Linear) ->
            (e_223 : (TEq#0 A_218 x_219 y_220)) ->
              (f_224 : (P_221) x_219) -> (P_221) y_220).

Inductive TUnit#2 : Type :=
| Dtt#3 : TUnit#2.

Inductive TNat#4 : Type :=
| DO#5 : TNat#4
| DS#6 : (TNat#4) -> TNat#4.

Inductive TBool#7 : Type :=
| Dtrue#8 : TBool#7
| Dfalse#9 : TBool#7.

Inductive TSigma#10 (A_226 : Type) (F_227 : A_226 -> Type) : Type :=
| Dpair#11 (A_229 : Type)
             (F_230 : A_229 -> Type)
               : (x_232 : A_229) ->
                   ((F_230) x_232) -> (TSigma#10 A_229 F_230).

Inductive TTensor#12 (A_234 : Linear) (B_235 : Linear) : Linear :=
| Dtpair#13 (A_236 : Linear)
              (B_237 : Linear)
                : (A_236) -> (B_237) -> (TTensor#12 A_236 B_237).

Inductive TFTensor#14 (A_240 : Type) (F_241 : A_240 -> Linear) : Linear :=
| Dfpair#15 (A_243 : Type)
              (F_244 : A_243 -> Linear)
                : (x_246 : A_243) ->
                    ((F_244) x_246) -> (TFTensor#14 A_243 F_244).

Definition Loc_248 := ((TNat#4) : Type).

Axiom PtsTo_249 : Loc_248 -> Type -> Linear.

Definition Ptr_252 :=
  ((fun A_253 => (TFTensor#14 Loc_248 fun l_254 => ((PtsTo_249) l_254) A_253)) :
    (A_255 : Type) -> Linear).

Axiom New_256 : (A_257 : Type) -> A_257 -> (Ptr_252) A_257.

Axiom Free_259 : (A_260 : Type) -> (Ptr_252) A_260 -> TUnit#2.

Axiom Get_262 :
  (A_263 : Type) ->
    (l_264 : Loc_248) ->
      ((PtsTo_249) l_264) A_263 ->
        (TFTensor#14 A_263 fun __266 => ((PtsTo_249) l_264) A_263).

Axiom Set_267 :
  (A_268 : Type) ->
    (B_269 : Type) ->
      B_269 ->
        (l_271 : Loc_248) ->
          ((PtsTo_249) l_271) A_268 -> ((PtsTo_249) l_271) B_269.

Definition lnId_273 :=
  ((fun A_274 => A_274 >> A_274) : (A_276 : Type) -> Linear).

Definition add_277 :=
  ((fix add_278 m_279 n_280 =>
      match m_279 with
      | (DO#5 ) => n_280
      | (DS#6 m_281) => (DS#6 ((add_278) m_281) n_280)
      end) :
    (m_282 : TNat#4) -> (n_283 : TNat#4) -> TNat#4).

Inductive TFin#21 : (TNat#4) -> Type :=
| DF1#22 : (n_285 : TNat#4) -> (TFin#21 (DS#6 n_285))
| DFS#23 : (n_286 : TNat#4) -> ((TFin#21 n_286)) -> (TFin#21 (DS#6 n_286)).

Inductive TArrVec#24 (A_288 : Type) (l_289 : Loc_248) : (TNat#4) -> Linear :=
| DNil#25 (A_291 : Type) (l_292 : Loc_248) : (TArrVec#24 A_291 l_292 DO#5)
| DCons#26 (A_293 : Type)
             (l_294 : Loc_248)
               : (n_295 : TNat#4) ->
                   (((PtsTo_249) ((add_277) l_294) n_295) A_293) ->
                     ((TArrVec#24 A_293 l_294 n_295)) ->
                       (TArrVec#24 A_293 l_294 (DS#6 n_295)).

Definition Array_298 :=
  ((fun A_299 n_300 =>
      (TFTensor#14 Loc_248 fun l_301 => (TArrVec#24 A_299 l_301 n_300))) :
    (A_302 : Type) -> (n_303 : TNat#4) -> Linear).

Definition First_304 :=
  ((fun A_305 n_306 arr_307 =>
      let x_308 := arr_307 in
      match x_308 with
      | (Dfpair#15 l_309 v_310) =>
        (match v_310 in (TArrVec#24 __312 __313 n1_314) return
           match n1_314 with
           | (DO#5 ) => (TEq#0 TNat#4 n_306 n_306) >> (lnId_273) A_305
           | (DS#6 n2_316) =>
             (TEq#0 TNat#4 n2_316 n_306) >>
               (TFTensor#14
                 A_305 fun __318 => ((Array_298) A_305) (DS#6 n_306))
           end
         with
         | (DNil#25 ) => fun __319 x_320 => x_320
         | (DCons#26 n1_321 c_322 v_323) =>
           fun pf_324 =>
             let f1_325 :=
               ((fun n_326 => ((PtsTo_249) ((add_277) l_309) n_326) A_305) :
                 TNat#4 -> Linear)
             in
             let f2_328 :=
               ((fun n_329 => (TArrVec#24 A_305 l_309 n_329)) :
                 TNat#4 -> Linear)
             in
             let c_331 :=
               ((((((LnInd_207) TNat#4) n1_321) n_306) f1_325) pf_324) c_322
             in
             let v_332 :=
               ((((((LnInd_207) TNat#4) n1_321) n_306) f2_328) pf_324) v_323
             in
             let x_333 := (((Get_262) A_305) ((add_277) l_309) n_306) c_331
             in
             match x_333 with
             | (Dfpair#15 x_334 c_335) =>
               (Dfpair#15 x_334
                            (Dfpair#15 l_309 (DCons#26 n_306 c_335 v_332)))
             end
         end) Drefl#1
      end) :
    (A_336 : Type) ->
      (n_337 : TNat#4) ->
        (arr_338 : ((Array_298) A_336) (DS#6 n_337)) ->
          (TFTensor#14 A_336 fun __339 => ((Array_298) A_336) (DS#6 n_337))).

Definition main_340 := ((Dtt#3) : TUnit#2).



v_ctx  := {
  main :0 (TUnit#2)::w
  First :0
    ((A_3313 : Type) ->
       (n_3314 : TNat#4) ->
         (arr_3315 :
           ((((fun A_3316 n_3317 =>
                 (TFTensor#14
                   ((TNat#4) : Type)
                     fun l_3318 => (TArrVec#24 A_3316 l_3318 n_3317))) :
               (A_3319 : Type) -> (n_3320 : TNat#4) -> Linear))
              A_3313)
             (DS#6 n_3314)) ->
           (TFTensor#14
             A_3313
               fun __3321 =>
                 ((((fun A_3322 n_3323 =>
                       (TFTensor#14
                         ((TNat#4) : Type)
                           fun l_3324 => (TArrVec#24 A_3322 l_3324 n_3323))) :
                     (A_3325 : Type) -> (n_3326 : TNat#4) -> Linear))
                    A_3313)
                   (DS#6 n_3314)))::w
  Array :0 ((A_3327 : Type) -> (n_3328 : TNat#4) -> Linear)::w
  add :0 ((m_3329 : TNat#4) -> (n_3330 : TNat#4) -> TNat#4)::w
  lnId :0 ((A_3331 : Type) -> Linear)::w
  Set :0
    ((A_3332 : Type) ->
       (B_3333 : Type) ->
         B_3333 ->
           (l_3335 : ((TNat#4) : Type)) ->
             ((DPtsTo#16) l_3335) A_3332 -> ((DPtsTo#16) l_3335) B_3333)::w
  Get :0
    ((A_3337 : Type) ->
       (l_3338 : ((TNat#4) : Type)) ->
         ((DPtsTo#16) l_3338) A_3337 ->
           (TFTensor#14 A_3337 fun __3340 => ((DPtsTo#16) l_3338) A_3337))::w
  Free :0
    ((A_3341 : Type) ->
       (((fun A_3343 =>
            (TFTensor#14
              ((TNat#4) : Type) fun l_3344 => ((DPtsTo#16) l_3344) A_3343)) :
          (A_3345 : Type) -> Linear))
         A_3341 -> TUnit#2)::w
  New :0
    ((A_3346 : Type) ->
       A_3346 ->
         (((fun A_3348 =>
              (TFTensor#14
                ((TNat#4) : Type) fun l_3349 => ((DPtsTo#16) l_3349) A_3348)) :
            (A_3350 : Type) -> Linear))
           A_3346)::w
  Ptr :0 ((A_3351 : Type) -> Linear)::w
  PtsTo :0 (((TNat#4) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  LnInd :0
    ((A_3354 : Type) ->
       (x_3355 : A_3354) ->
         (y_3356 : A_3354) ->
           (P_3357 : A_3354 -> Linear) ->
             (e_3359 : (TEq#0 A_3354 x_3355 y_3356)) ->
               (f_3360 : (P_3357) x_3355) -> (P_3357) y_3356)::w
  TyInd :0
    ((A_3361 : Type) ->
       (x_3362 : A_3361) ->
         (y_3363 : A_3361) ->
           (P_3364 : A_3361 -> Type) ->
             (e_3366 : (TEq#0 A_3361 x_3362 y_3363)) ->
               (f_3367 : (P_3364) x_3362) -> (P_3364) y_3363)::w
  Eq_sym :0
    ((A_3368 : Type) ->
       (x_3369 : A_3368) ->
         (y_3370 : A_3368) ->
           (e_3371 : (TEq#0 A_3368 x_3369 y_3370)) ->
             (TEq#0 A_3368 y_3370 x_3369))::w
}

Dtt#3

