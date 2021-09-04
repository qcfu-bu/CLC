Inductive Eq_0 (A_1 : Type) (x_2 : A_1) : (A_1) -> Type :=
| refl_1 (A_1 : Type) (x_2 : A_1) : (Eq_0 A_1 x_2 x_2).

Definition Eq_trans_3 :=
  ((fun A_4 x_5 y_6 z_7 e1_8 e2_9 =>
      match e2_9 in (Eq_0 __0 __0 y_6) return (Eq_0 A_4 x_5 y_6) with
      | (refl_1 ) => e1_8
      end) :
    (A_4 : Type) ->
      (x_5 : A_4) ->
        (y_6 : A_4) ->
          (z_7 : A_4) ->
            (e1_8 : (Eq_0 A_4 x_5 y_6)) ->
              (e2_9 : (Eq_0 A_4 y_6 z_7)) -> (Eq_0 A_4 x_5 z_7)).

Definition Eq_sym_10 :=
  ((fun A_11 x_12 y_13 e_14 =>
      match e_14 in (Eq_0 __0 __0 y_13) return (Eq_0 A_11 y_13 x_12) with
      | (refl_1 ) => refl_1
      end) :
    (A_11 : Type) ->
      (x_12 : A_11) ->
        (y_13 : A_11) ->
          (e_14 : (Eq_0 A_11 x_12 y_13)) -> (Eq_0 A_11 y_13 x_12)).

Definition TyInd_15 :=
  ((fun A_16 x_17 y_18 P_19 e_20 f_21 =>
      match e_20 in (Eq_0 __0 __0 y_18) return (P_19) y_18 with
      | (refl_1 ) => f_21
      end) :
    (A_16 : Type) ->
      (x_17 : A_16) ->
        (y_18 : A_16) ->
          (P_19 : A_16 -> Type) ->
            (e_20 : (Eq_0 A_16 x_17 y_18)) ->
              (f_21 : (P_19) x_17) -> (P_19) y_18).

Definition LnInd_22 :=
  ((fun A_23 x_24 y_25 P_26 e_27 f_28 =>
      match e_27 in (Eq_0 __0 __0 y_25) return (P_26) y_25 with
      | (refl_1 ) => f_28
      end) :
    (A_23 : Type) ->
      (x_24 : A_23) ->
        (y_25 : A_23) ->
          (P_26 : A_23 -> Linear) ->
            (e_27 : (Eq_0 A_23 x_24 y_25)) ->
              (f_28 : (P_26) x_24) -> (P_26) y_25).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_29 :=
  ((fix add_29 m_30 n_31 =>
      match m_30 with
      | (O_7 ) => n_31
      | (S_8 m_30) => (S_8 ((add_29) m_30) n_31)
      end) :
    (m_30 : Nat_6) -> (n_31 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_32 : Type) (F_33 : A_32 -> Type) : Type :=
| pair_13 (A_32 : Type)
            (F_33 : A_32 -> Type)
              : (x_35 : A_32) -> ((F_33) x_35) -> (Sigma_12 A_32 F_33).

Inductive Tensor_14 (A_36 : Linear) (B_37 : Linear) : Linear :=
| tpair_15 (A_36 : Linear)
             (B_37 : Linear) : (A_36) -> (B_37) -> (Tensor_14 A_36 B_37).

Inductive FTensor_16 (A_38 : Type) (F_39 : A_38 -> Linear) : Linear :=
| fpair_17 (A_38 : Type)
             (F_39 : A_38 -> Linear)
               : (x_41 : A_38) -> ((F_39) x_41) -> (FTensor_16 A_38 F_39).

Axiom unsafeC_42 : (A_44 : Linear) -> A_44 -> Unit_2.

Axiom unsafeP_45 : (A_47 : Linear) -> A_47.

Definition Loc_48 := ((Nat_6) : Type).

Axiom PtsTo_49 : Loc_48 -> Type -> Linear.

Definition Ptr_50 :=
  ((fun A_51 => (FTensor_16 Loc_48 fun l_52 => ((PtsTo_49) l_52) A_51)) :
    (A_51 : Type) -> Linear).

Axiom New_53 : (A_55 : Type) -> A_55 -> (Ptr_50) A_55.

Axiom Free_56 : (A_58 : Type) -> (Ptr_50) A_58 -> Unit_2.

Axiom Get_59 :
  (A_61 : Type) ->
    (l_63 : Loc_48) ->
      ((PtsTo_49) l_63) A_61 ->
        (FTensor_16 A_61 fun __0 => ((PtsTo_49) l_63) A_61).

Axiom Set_64 :
  (A_66 : Type) ->
    (B_68 : Type) ->
      B_68 ->
        (l_70 : Loc_48) -> ((PtsTo_49) l_70) A_66 -> ((PtsTo_49) l_70) B_68.

Axiom ptsto_71 : (A_75 : Type) -> Nat_6 -> A_75 -> Linear.

Axiom new_76 :
  (A_80 : Type) ->
    (x_84 : A_80) ->
      (FTensor_16 Nat_6 fun l_85 => (((ptsto_71) ?0) l_85) x_84).

Axiom free_86 :
  (A_90 : Type) ->
    (l_94 : Nat_6) -> (x_98 : A_90) -> (((ptsto_71) ?1) l_94) x_98 -> Unit_2.

Axiom get_99 :
  (A_103 : Type) ->
    (l_107 : Nat_6) ->
      (x_111 : A_103) ->
        (((ptsto_71) ?2) l_107) x_111 ->
          (FTensor_16
            (Sigma_12 A_103 fun y_112 => (Eq_0 ?3 x_111 y_112))
              fun __0 => (((ptsto_71) ?4) l_107) x_111).

Axiom set_113 :
  (A_119 : Type) ->
    (B_120 : Type) ->
      (l_124 : Nat_6) ->
        (x_128 : A_119) ->
          (((ptsto_71) ?5) l_124) x_128 ->
            (y_132 : B_120) -> (((ptsto_71) ?6) l_124) y_132.

Definition main_133 :=
  ((let (fpair_17 __0 c_134) := ((new_76) ?7) (S_8 O_7) in
    let (fpair_17 xeq_136 c_134) := ((((get_99) ?8) ?9) ?10) c_134 in
    let (fpair_17 yeq_138 c_134) := ((((get_99) ?11) ?12) ?13) c_134 in
    let (pair_13 x_139 pf1_140) := xeq_136 in
    let (pair_13 y_141 pf2_142) := yeq_138 in
    let pf1_140 := ((((Eq_sym_10) ?14) ?15) ?16) pf1_140 in
    let pf_143 :=
      ((((((((Eq_trans_3) ?18) ?19) ?20) ?21) pf1_140) pf2_142) :
        (Eq_0 ?17 x_139 y_141))
    in ((((free_86) ?22) ?23) ?24) c_134) : Unit_2).



Inductive Eq_0 (A_177 : Type) (x_178 : A_177) : (A_177) -> Type :=
| refl_1 (A_180 : Type) (x_181 : A_180) : (Eq_0 A_180 x_181 x_181).

Definition Eq_trans_182 :=
  ((fun A_183 x_184 y_185 z_186 e1_187 e2_188 =>
      match e2_188 in (Eq_0 __190 __191 y_192) return
        (Eq_0 A_183 x_184 y_192)
      with
      | (refl_1 ) => e1_187
      end) :
    (A_193 : Type) ->
      (x_194 : A_193) ->
        (y_195 : A_193) ->
          (z_196 : A_193) ->
            (e1_197 : (Eq_0 A_193 x_194 y_195)) ->
              (e2_198 : (Eq_0 A_193 y_195 z_196)) -> (Eq_0 A_193 x_194 z_196)).

Definition Eq_sym_199 :=
  ((fun A_200 x_201 y_202 e_203 =>
      match e_203 in (Eq_0 __205 __206 y_207) return (Eq_0 A_200 y_207 x_201)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_208 : Type) ->
      (x_209 : A_208) ->
        (y_210 : A_208) ->
          (e_211 : (Eq_0 A_208 x_209 y_210)) -> (Eq_0 A_208 y_210 x_209)).

Definition TyInd_212 :=
  ((fun A_213 x_214 y_215 P_216 e_217 f_218 =>
      match e_217 in (Eq_0 __220 __221 y_222) return (P_216) y_222 with
      | (refl_1 ) => f_218
      end) :
    (A_223 : Type) ->
      (x_224 : A_223) ->
        (y_225 : A_223) ->
          (P_226 : (A_223) -> Type) ->
            (e_228 : (Eq_0 A_223 x_224 y_225)) ->
              (f_229 : (P_226) x_224) -> (P_226) y_225).

Definition LnInd_230 :=
  ((fun A_231 x_232 y_233 P_234 e_235 f_236 =>
      match e_235 in (Eq_0 __238 __239 y_240) return (P_234) y_240 with
      | (refl_1 ) => f_236
      end) :
    (A_241 : Type) ->
      (x_242 : A_241) ->
        (y_243 : A_241) ->
          (P_244 : (A_241) -> Linear) ->
            (e_246 : (Eq_0 A_241 x_242 y_243)) ->
              (f_247 : (P_244) x_242) -> (P_244) y_243).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_249 :=
  ((fix add_250 m_251 n_252 =>
      match m_251 with
      | (O_7 ) => n_252
      | (S_8 m_253) => (S_8 ((add_250) m_253) n_252)
      end) :
    (m_254 : Nat_6) -> (n_255 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_256 : Type) (F_257 : (A_256) -> Type) : Type :=
| pair_13 (A_259 : Type)
            (F_260 : (A_259) -> Type)
              : (x_262 : A_259) -> ((F_260) x_262) -> (Sigma_12 A_259 F_260).

Inductive Tensor_14 (A_264 : Linear) (B_265 : Linear) : Linear :=
| tpair_15 (A_266 : Linear)
             (B_267 : Linear) : (A_266) -> (B_267) -> (Tensor_14 A_266 B_267).

Inductive FTensor_16 (A_270 : Type) (F_271 : (A_270) -> Linear) : Linear :=
| fpair_17 (A_273 : Type)
             (F_274 : (A_273) -> Linear)
               : (x_276 : A_273) ->
                   ((F_274) x_276) -> (FTensor_16 A_273 F_274).

Axiom unsafeC_278 : (A_279 : Linear) -> (A_279) -> Unit_2.

Axiom unsafeP_281 : (A_282 : Linear) -> A_282.

Definition Loc_283 := ((Nat_6) : Type).

Axiom PtsTo_284 : (Loc_283) -> (Type) -> Linear.

Definition Ptr_287 :=
  ((fun A_288 => (FTensor_16 Loc_283 fun l_289 => ((PtsTo_284) l_289) A_288)) :
    (A_290 : Type) -> Linear).

Axiom New_291 : (A_292 : Type) -> (A_292) -> (Ptr_287) A_292.

Axiom Free_294 : (A_295 : Type) -> ((Ptr_287) A_295) -> Unit_2.

Axiom Get_297 :
  (A_298 : Type) ->
    (l_299 : Loc_283) ->
      (((PtsTo_284) l_299) A_298) ->
        (FTensor_16 A_298 fun __301 => ((PtsTo_284) l_299) A_298).

Axiom Set_302 :
  (A_303 : Type) ->
    (B_304 : Type) ->
      (B_304) ->
        (l_306 : Loc_283) ->
          (((PtsTo_284) l_306) A_303) -> ((PtsTo_284) l_306) B_304.

Axiom ptsto_308 : (A_309 : Type) -> (Nat_6) -> (A_309) -> Linear.

Axiom new_312 :
  (A_313 : Type) ->
    (x_314 : A_313) ->
      (FTensor_16
        Nat_6
          fun l_315 =>
            (((ptsto_308)
                ((((((((((((((((((?0) Eq_trans_182) Eq_sym_199) TyInd_212)
                                LnInd_230)
                               add_249)
                              unsafeC_278)
                             unsafeP_281)
                            Loc_283)
                           PtsTo_284)
                          Ptr_287)
                         New_291)
                        Free_294)
                       Get_297)
                      Set_302)
                     ptsto_308)
                    A_313)
                   x_314)
                  l_315)
               l_315)
              x_314).

Axiom free_316 :
  (A_317 : Type) ->
    (l_318 : Nat_6) ->
      (x_319 : A_317) ->
        ((((ptsto_308)
             (((((((((((((((((((?1) Eq_trans_182) Eq_sym_199) TyInd_212)
                              LnInd_230)
                             add_249)
                            unsafeC_278)
                           unsafeP_281)
                          Loc_283)
                         PtsTo_284)
                        Ptr_287)
                       New_291)
                      Free_294)
                     Get_297)
                    Set_302)
                   ptsto_308)
                  new_312)
                 A_317)
                l_318)
               x_319)
            l_318)
           x_319) ->
          Unit_2.

Axiom get_321 :
  (A_322 : Type) ->
    (l_323 : Nat_6) ->
      (x_324 : A_322) ->
        ((((ptsto_308)
             ((((((((((((((((((((?2) Eq_trans_182) Eq_sym_199) TyInd_212)
                               LnInd_230)
                              add_249)
                             unsafeC_278)
                            unsafeP_281)
                           Loc_283)
                          PtsTo_284)
                         Ptr_287)
                        New_291)
                       Free_294)
                      Get_297)
                     Set_302)
                    ptsto_308)
                   new_312)
                  free_316)
                 A_322)
                l_323)
               x_324)
            l_323)
           x_324) ->
          (FTensor_16
            (Sigma_12
              A_322
                fun y_326 =>
                  (Eq_0
                    ((((((((((((((((((((((?3) __325) Eq_trans_182) Eq_sym_199)
                                        TyInd_212)
                                       LnInd_230)
                                      add_249)
                                     unsafeC_278)
                                    unsafeP_281)
                                   Loc_283)
                                  PtsTo_284)
                                 Ptr_287)
                                New_291)
                               Free_294)
                              Get_297)
                             Set_302)
                            ptsto_308)
                           new_312)
                          free_316)
                         A_322)
                        l_323)
                       x_324)
                      y_326 x_324 y_326))
              fun __327 =>
                (((ptsto_308)
                    (((((((((((((((((((((?4) __327) Eq_trans_182) Eq_sym_199)
                                       TyInd_212)
                                      LnInd_230)
                                     add_249)
                                    unsafeC_278)
                                   unsafeP_281)
                                  Loc_283)
                                 PtsTo_284)
                                Ptr_287)
                               New_291)
                              Free_294)
                             Get_297)
                            Set_302)
                           ptsto_308)
                          new_312)
                         free_316)
                        A_322)
                       l_323)
                      x_324)
                   l_323)
                  x_324).

Axiom set_328 :
  (A_329 : Type) ->
    (B_330 : Type) ->
      (l_331 : Nat_6) ->
        (x_332 : A_329) ->
          ((((ptsto_308)
               ((((((((((((((((((((((?5) Eq_trans_182) Eq_sym_199) TyInd_212)
                                   LnInd_230)
                                  add_249)
                                 unsafeC_278)
                                unsafeP_281)
                               Loc_283)
                              PtsTo_284)
                             Ptr_287)
                            New_291)
                           Free_294)
                          Get_297)
                         Set_302)
                        ptsto_308)
                       new_312)
                      free_316)
                     get_321)
                    A_329)
                   B_330)
                  l_331)
                 x_332)
              l_331)
             x_332) ->
            (y_334 : B_330) ->
              (((ptsto_308)
                  ((((((((((((((((((((((((?6) __333) Eq_trans_182) Eq_sym_199)
                                        TyInd_212)
                                       LnInd_230)
                                      add_249)
                                     unsafeC_278)
                                    unsafeP_281)
                                   Loc_283)
                                  PtsTo_284)
                                 Ptr_287)
                                New_291)
                               Free_294)
                              Get_297)
                             Set_302)
                            ptsto_308)
                           new_312)
                          free_316)
                         get_321)
                        A_329)
                       B_330)
                      l_331)
                     x_332)
                    y_334)
                 l_331)
                y_334.

Definition main_335 :=
  ((let x_336 :=
      ((new_312)
         (((((((((((((((((((?7) Eq_trans_182) Eq_sym_199) TyInd_212)
                          LnInd_230)
                         add_249)
                        unsafeC_278)
                       unsafeP_281)
                      Loc_283)
                     PtsTo_284)
                    Ptr_287)
                   New_291)
                  Free_294)
                 Get_297)
                Set_302)
               ptsto_308)
              new_312)
             free_316)
            get_321)
           set_328)
        (S_8 O_7)
    in
    match x_336 with
    | (fpair_17 __337 c_338) =>
      let x_339 :=
        ((((get_321)
             (((((((((((((((((((((?8) __337) Eq_trans_182) Eq_sym_199)
                                TyInd_212)
                               LnInd_230)
                              add_249)
                             unsafeC_278)
                            unsafeP_281)
                           Loc_283)
                          PtsTo_284)
                         Ptr_287)
                        New_291)
                       Free_294)
                      Get_297)
                     Set_302)
                    ptsto_308)
                   new_312)
                  free_316)
                 get_321)
                set_328)
               c_338)
            (((((((((((((((((((((?9) __337) Eq_trans_182) Eq_sym_199)
                               TyInd_212)
                              LnInd_230)
                             add_249)
                            unsafeC_278)
                           unsafeP_281)
                          Loc_283)
                         PtsTo_284)
                        Ptr_287)
                       New_291)
                      Free_294)
                     Get_297)
                    Set_302)
                   ptsto_308)
                  new_312)
                 free_316)
                get_321)
               set_328)
              c_338)
           (((((((((((((((((((((?10) __337) Eq_trans_182) Eq_sym_199)
                              TyInd_212)
                             LnInd_230)
                            add_249)
                           unsafeC_278)
                          unsafeP_281)
                         Loc_283)
                        PtsTo_284)
                       Ptr_287)
                      New_291)
                     Free_294)
                    Get_297)
                   Set_302)
                  ptsto_308)
                 new_312)
                free_316)
               get_321)
              set_328)
             c_338)
          c_338
      in
      match x_339 with
      | (fpair_17 xeq_340 c_341) =>
        let x_342 :=
          ((((get_321)
               ((((((((((((((((((((((?11) __337) Eq_trans_182) Eq_sym_199)
                                   TyInd_212)
                                  LnInd_230)
                                 add_249)
                                unsafeC_278)
                               unsafeP_281)
                              Loc_283)
                             PtsTo_284)
                            Ptr_287)
                           New_291)
                          Free_294)
                         Get_297)
                        Set_302)
                       ptsto_308)
                      new_312)
                     free_316)
                    get_321)
                   set_328)
                  c_341)
                 xeq_340)
              ((((((((((((((((((((((?12) __337) Eq_trans_182) Eq_sym_199)
                                  TyInd_212)
                                 LnInd_230)
                                add_249)
                               unsafeC_278)
                              unsafeP_281)
                             Loc_283)
                            PtsTo_284)
                           Ptr_287)
                          New_291)
                         Free_294)
                        Get_297)
                       Set_302)
                      ptsto_308)
                     new_312)
                    free_316)
                   get_321)
                  set_328)
                 c_341)
                xeq_340)
             ((((((((((((((((((((((?13) __337) Eq_trans_182) Eq_sym_199)
                                 TyInd_212)
                                LnInd_230)
                               add_249)
                              unsafeC_278)
                             unsafeP_281)
                            Loc_283)
                           PtsTo_284)
                          Ptr_287)
                         New_291)
                        Free_294)
                       Get_297)
                      Set_302)
                     ptsto_308)
                    new_312)
                   free_316)
                  get_321)
                 set_328)
                c_341)
               xeq_340)
            c_341
        in
        match x_342 with
        | (fpair_17 yeq_343 c_344) =>
          let x_345 := xeq_340 in
          match x_345 with
          | (pair_13 x_346 pf1_347) =>
            let x0_348 := yeq_343 in
            match x0_348 with
            | (pair_13 y_349 pf2_350) =>
              let pf1_351 :=
                ((((Eq_sym_199)
                     (((((((((((((((((((((((((((?14) __337) Eq_trans_182)
                                               Eq_sym_199)
                                              TyInd_212)
                                             LnInd_230)
                                            add_249)
                                           unsafeC_278)
                                          unsafeP_281)
                                         Loc_283)
                                        PtsTo_284)
                                       Ptr_287)
                                      New_291)
                                     Free_294)
                                    Get_297)
                                   Set_302)
                                  ptsto_308)
                                 new_312)
                                free_316)
                               get_321)
                              set_328)
                             c_344)
                            xeq_340)
                           yeq_343)
                          x_346)
                         pf1_347)
                        y_349)
                       pf2_350)
                    (((((((((((((((((((((((((((?15) __337) Eq_trans_182)
                                              Eq_sym_199)
                                             TyInd_212)
                                            LnInd_230)
                                           add_249)
                                          unsafeC_278)
                                         unsafeP_281)
                                        Loc_283)
                                       PtsTo_284)
                                      Ptr_287)
                                     New_291)
                                    Free_294)
                                   Get_297)
                                  Set_302)
                                 ptsto_308)
                                new_312)
                               free_316)
                              get_321)
                             set_328)
                            c_344)
                           xeq_340)
                          yeq_343)
                         x_346)
                        pf1_347)
                       y_349)
                      pf2_350)
                   (((((((((((((((((((((((((((?16) __337) Eq_trans_182)
                                             Eq_sym_199)
                                            TyInd_212)
                                           LnInd_230)
                                          add_249)
                                         unsafeC_278)
                                        unsafeP_281)
                                       Loc_283)
                                      PtsTo_284)
                                     Ptr_287)
                                    New_291)
                                   Free_294)
                                  Get_297)
                                 Set_302)
                                ptsto_308)
                               new_312)
                              free_316)
                             get_321)
                            set_328)
                           c_344)
                          xeq_340)
                         yeq_343)
                        x_346)
                       pf1_347)
                      y_349)
                     pf2_350)
                  pf1_347
              in
              let pf_352 :=
                ((((((((Eq_trans_182)
                         (((((((((((((((((((((((((((?18) __337) Eq_trans_182)
                                                   Eq_sym_199)
                                                  TyInd_212)
                                                 LnInd_230)
                                                add_249)
                                               unsafeC_278)
                                              unsafeP_281)
                                             Loc_283)
                                            PtsTo_284)
                                           Ptr_287)
                                          New_291)
                                         Free_294)
                                        Get_297)
                                       Set_302)
                                      ptsto_308)
                                     new_312)
                                    free_316)
                                   get_321)
                                  set_328)
                                 c_344)
                                xeq_340)
                               yeq_343)
                              x_346)
                             pf1_351)
                            y_349)
                           pf2_350)
                        (((((((((((((((((((((((((((?19) __337) Eq_trans_182)
                                                  Eq_sym_199)
                                                 TyInd_212)
                                                LnInd_230)
                                               add_249)
                                              unsafeC_278)
                                             unsafeP_281)
                                            Loc_283)
                                           PtsTo_284)
                                          Ptr_287)
                                         New_291)
                                        Free_294)
                                       Get_297)
                                      Set_302)
                                     ptsto_308)
                                    new_312)
                                   free_316)
                                  get_321)
                                 set_328)
                                c_344)
                               xeq_340)
                              yeq_343)
                             x_346)
                            pf1_351)
                           y_349)
                          pf2_350)
                       (((((((((((((((((((((((((((?20) __337) Eq_trans_182)
                                                 Eq_sym_199)
                                                TyInd_212)
                                               LnInd_230)
                                              add_249)
                                             unsafeC_278)
                                            unsafeP_281)
                                           Loc_283)
                                          PtsTo_284)
                                         Ptr_287)
                                        New_291)
                                       Free_294)
                                      Get_297)
                                     Set_302)
                                    ptsto_308)
                                   new_312)
                                  free_316)
                                 get_321)
                                set_328)
                               c_344)
                              xeq_340)
                             yeq_343)
                            x_346)
                           pf1_351)
                          y_349)
                         pf2_350)
                      (((((((((((((((((((((((((((?21) __337) Eq_trans_182)
                                                Eq_sym_199)
                                               TyInd_212)
                                              LnInd_230)
                                             add_249)
                                            unsafeC_278)
                                           unsafeP_281)
                                          Loc_283)
                                         PtsTo_284)
                                        Ptr_287)
                                       New_291)
                                      Free_294)
                                     Get_297)
                                    Set_302)
                                   ptsto_308)
                                  new_312)
                                 free_316)
                                get_321)
                               set_328)
                              c_344)
                             xeq_340)
                            yeq_343)
                           x_346)
                          pf1_351)
                         y_349)
                        pf2_350)
                     pf1_351)
                    pf2_350) :
                  (Eq_0
                    (((((((((((((((((((((((((((?17) __337) Eq_trans_182)
                                              Eq_sym_199)
                                             TyInd_212)
                                            LnInd_230)
                                           add_249)
                                          unsafeC_278)
                                         unsafeP_281)
                                        Loc_283)
                                       PtsTo_284)
                                      Ptr_287)
                                     New_291)
                                    Free_294)
                                   Get_297)
                                  Set_302)
                                 ptsto_308)
                                new_312)
                               free_316)
                              get_321)
                             set_328)
                            c_344)
                           xeq_340)
                          yeq_343)
                         x_346)
                        pf1_351)
                       y_349)
                      pf2_350 x_346 y_349))
              in
              ((((free_316)
                   ((((((((((((((((((((((((((((?22) __337) Eq_trans_182)
                                              Eq_sym_199)
                                             TyInd_212)
                                            LnInd_230)
                                           add_249)
                                          unsafeC_278)
                                         unsafeP_281)
                                        Loc_283)
                                       PtsTo_284)
                                      Ptr_287)
                                     New_291)
                                    Free_294)
                                   Get_297)
                                  Set_302)
                                 ptsto_308)
                                new_312)
                               free_316)
                              get_321)
                             set_328)
                            c_344)
                           xeq_340)
                          yeq_343)
                         x_346)
                        pf1_351)
                       y_349)
                      pf2_350)
                     pf_352)
                  ((((((((((((((((((((((((((((?23) __337) Eq_trans_182)
                                             Eq_sym_199)
                                            TyInd_212)
                                           LnInd_230)
                                          add_249)
                                         unsafeC_278)
                                        unsafeP_281)
                                       Loc_283)
                                      PtsTo_284)
                                     Ptr_287)
                                    New_291)
                                   Free_294)
                                  Get_297)
                                 Set_302)
                                ptsto_308)
                               new_312)
                              free_316)
                             get_321)
                            set_328)
                           c_344)
                          xeq_340)
                         yeq_343)
                        x_346)
                       pf1_351)
                      y_349)
                     pf2_350)
                    pf_352)
                 ((((((((((((((((((((((((((((?24) __337) Eq_trans_182)
                                            Eq_sym_199)
                                           TyInd_212)
                                          LnInd_230)
                                         add_249)
                                        unsafeC_278)
                                       unsafeP_281)
                                      Loc_283)
                                     PtsTo_284)
                                    Ptr_287)
                                   New_291)
                                  Free_294)
                                 Get_297)
                                Set_302)
                               ptsto_308)
                              new_312)
                             free_316)
                            get_321)
                           set_328)
                          c_344)
                         xeq_340)
                        yeq_343)
                       x_346)
                      pf1_351)
                     y_349)
                    pf2_350)
                   pf_352)
                c_344
            end
          end
        end
      end
    end) : Unit_2).



Inductive Eq_0 (A_106148 : Type) (x_106149 : A_106148) : (A_106148) -> Type :=
| refl_1 (A_106151 : Type)
           (x_106152 : A_106151) : (Eq_0 A_106151 x_106152 x_106152).

Definition Eq_trans_106153 :=
  ((fun A_106154 x_106155 y_106156 z_106157 e1_106158 e2_106159 =>
      match e2_106159 in (Eq_0 __106161 __106162 y_106163) return
        (Eq_0 A_106154 x_106155 y_106163)
      with
      | (refl_1 ) => e1_106158
      end) :
    (A_106164 : Type) ->
      (x_106165 : A_106164) ->
        (y_106166 : A_106164) ->
          (z_106167 : A_106164) ->
            (e1_106168 : (Eq_0 A_106164 x_106165 y_106166)) ->
              (e2_106169 : (Eq_0 A_106164 y_106166 z_106167)) ->
                (Eq_0 A_106164 x_106165 z_106167)).

Definition Eq_sym_106170 :=
  ((fun A_106171 x_106172 y_106173 e_106174 =>
      match e_106174 in (Eq_0 __106176 __106177 y_106178) return
        (Eq_0 A_106171 y_106178 x_106172)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_106179 : Type) ->
      (x_106180 : A_106179) ->
        (y_106181 : A_106179) ->
          (e_106182 : (Eq_0 A_106179 x_106180 y_106181)) ->
            (Eq_0 A_106179 y_106181 x_106180)).

Definition TyInd_106183 :=
  ((fun A_106184 x_106185 y_106186 P_106187 e_106188 f_106189 =>
      match e_106188 in (Eq_0 __106191 __106192 y_106193) return
        (P_106187) y_106193
      with
      | (refl_1 ) => f_106189
      end) :
    (A_106194 : Type) ->
      (x_106195 : A_106194) ->
        (y_106196 : A_106194) ->
          (P_106197 : (A_106194) -> Type) ->
            (e_106199 : (Eq_0 A_106194 x_106195 y_106196)) ->
              (f_106200 : (P_106197) x_106195) -> (P_106197) y_106196).

Definition LnInd_106201 :=
  ((fun A_106202 x_106203 y_106204 P_106205 e_106206 f_106207 =>
      match e_106206 in (Eq_0 __106209 __106210 y_106211) return
        (P_106205) y_106211
      with
      | (refl_1 ) => f_106207
      end) :
    (A_106212 : Type) ->
      (x_106213 : A_106212) ->
        (y_106214 : A_106212) ->
          (P_106215 : (A_106212) -> Linear) ->
            (e_106217 : (Eq_0 A_106212 x_106213 y_106214)) ->
              (f_106218 : (P_106215) x_106213) -> (P_106215) y_106214).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_106220 :=
  ((fix add_106221 m_106222 n_106223 =>
      match m_106222 with
      | (O_7 ) => n_106223
      | (S_8 m_106224) => (S_8 ((add_106221) m_106224) n_106223)
      end) :
    (m_106225 : Nat_6) -> (n_106226 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_106227 : Type) (F_106228 : (A_106227) -> Type) : Type :=
| pair_13 (A_106230 : Type)
            (F_106231 : (A_106230) -> Type)
              : (x_106233 : A_106230) ->
                  ((F_106231) x_106233) -> (Sigma_12 A_106230 F_106231).

Inductive Tensor_14 (A_106235 : Linear) (B_106236 : Linear) : Linear :=
| tpair_15 (A_106237 : Linear)
             (B_106238 : Linear)
               : (A_106237) -> (B_106238) -> (Tensor_14 A_106237 B_106238).

Inductive FTensor_16 (A_106241 : Type)
                       (F_106242 : (A_106241) -> Linear) : Linear :=
| fpair_17 (A_106244 : Type)
             (F_106245 : (A_106244) -> Linear)
               : (x_106247 : A_106244) ->
                   ((F_106245) x_106247) -> (FTensor_16 A_106244 F_106245).

Axiom unsafeC_106249 : (A_106250 : Linear) -> (A_106250) -> Unit_2.

Axiom unsafeP_106252 : (A_106253 : Linear) -> A_106253.

Definition Loc_106254 := ((Nat_6) : Type).

Axiom PtsTo_106255 : (Loc_106254) -> (Type) -> Linear.

Definition Ptr_106258 :=
  ((fun A_106259 =>
      (FTensor_16
        Loc_106254 fun l_106260 => ((PtsTo_106255) l_106260) A_106259)) :
    (A_106261 : Type) -> Linear).

Axiom New_106262 : (A_106263 : Type) -> (A_106263) -> (Ptr_106258) A_106263.

Axiom Free_106265 : (A_106266 : Type) -> ((Ptr_106258) A_106266) -> Unit_2.

Axiom Get_106268 :
  (A_106269 : Type) ->
    (l_106270 : Loc_106254) ->
      (((PtsTo_106255) l_106270) A_106269) ->
        (FTensor_16
          A_106269 fun __106272 => ((PtsTo_106255) l_106270) A_106269).

Axiom Set_106273 :
  (A_106274 : Type) ->
    (B_106275 : Type) ->
      (B_106275) ->
        (l_106277 : Loc_106254) ->
          (((PtsTo_106255) l_106277) A_106274) ->
            ((PtsTo_106255) l_106277) B_106275.

Axiom ptsto_106279 : (A_106280 : Type) -> (Nat_6) -> (A_106280) -> Linear.

Axiom new_106283 :
  (A_106284 : Type) ->
    (x_106285 : A_106284) ->
      (FTensor_16
        Nat_6 fun l_106286 => (((ptsto_106279) A_106284) l_106286) x_106285).

Axiom free_106287 :
  (A_106288 : Type) ->
    (l_106289 : Nat_6) ->
      (x_106290 : A_106288) ->
        ((((ptsto_106279) A_106288) l_106289) x_106290) -> Unit_2.

Axiom get_106292 :
  (A_106293 : Type) ->
    (l_106294 : Nat_6) ->
      (x_106295 : A_106293) ->
        ((((ptsto_106279) A_106293) l_106294) x_106295) ->
          (FTensor_16
            (Sigma_12
              A_106293 fun y_106297 => (Eq_0 A_106293 x_106295 y_106297))
              fun __106298 => (((ptsto_106279) A_106293) l_106294) x_106295).

Axiom set_106299 :
  (A_106300 : Type) ->
    (B_106301 : Type) ->
      (l_106302 : Nat_6) ->
        (x_106303 : A_106300) ->
          ((((ptsto_106279) A_106300) l_106302) x_106303) ->
            (y_106305 : B_106301) ->
              (((ptsto_106279) B_106301) l_106302) y_106305.

Definition main_106306 :=
  ((let x_106307 := ((new_106283) Nat_6) (S_8 O_7) in
    match x_106307 with
    | (fpair_17 __106308 c_106309) =>
      let x_106310 := ((((get_106292) Nat_6) __106308) (S_8 O_7)) c_106309 in
      match x_106310 with
      | (fpair_17 xeq_106311 c_106312) =>
        let x_106313 := ((((get_106292) Nat_6) __106308) (S_8 O_7)) c_106312
        in
        match x_106313 with
        | (fpair_17 yeq_106314 c_106315) =>
          let x_106316 := xeq_106311 in
          match x_106316 with
          | (pair_13 x_106317 pf1_106318) =>
            let x0_106319 := yeq_106314 in
            match x0_106319 with
            | (pair_13 y_106320 pf2_106321) =>
              let pf1_106322 :=
                ((((Eq_sym_106170) Nat_6) (S_8 O_7)) x_106317) pf1_106318
              in
              let pf_106323 :=
                ((((((((Eq_trans_106153) Nat_6) x_106317) (S_8 O_7)) y_106320)
                     pf1_106322)
                    pf2_106321) :
                  (Eq_0 Nat_6 x_106317 y_106320))
              in ((((free_106287) Nat_6) __106308) (S_8 O_7)) c_106315
            end
          end
        end
      end
    end) : Unit_2).



match ((new_26) Nat_6) (S_8 O_7) with
| (fpair_17 __106645 c_106646) =>
  let x_106647 := ((((get_28) Nat_6) __106645) (S_8 O_7)) c_106646 in
  match x_106647 with
  | (fpair_17 xeq_106648 c_106649) =>
    let x_106650 := ((((get_28) Nat_6) __106645) (S_8 O_7)) c_106649 in
    match x_106650 with
    | (fpair_17 yeq_106651 c_106652) =>
      let x_106653 := xeq_106648 in
      match x_106653 with
      | (pair_13 x_106654 pf1_106655) =>
        let x0_106656 := yeq_106651 in
        match x0_106656 with
        | (pair_13 y_106657 pf2_106658) =>
          let pf1_106659 :=
            ((((fun A_106660 x_106661 y_106662 e_106663 =>
                  match e_106663 in (Eq_0 __106665 __106666 y_106667) return
                    (Eq_0 A_106660 y_106667 x_106661)
                  with
                  | (refl_1 ) => refl_1
                  end)
                 Nat_6)
                (S_8 O_7))
               x_106654)
              pf1_106655
          in
          let pf_106668 :=
            ((((((((fun A_106669 x_106670 y_106671 z_106672 e1_106673 e2_106674 =>
                      match e2_106674 in (Eq_0 __106676 __106677 y_106678) return
                        (Eq_0 A_106669 x_106670 y_106678)
                      with
                      | (refl_1 ) => e1_106673
                      end)
                     Nat_6)
                    x_106654)
                   (S_8 O_7))
                  y_106657)
                 pf1_106659)
                pf2_106658) :
              (Eq_0 Nat_6 x_106654 y_106657))
          in ((((free_27) Nat_6) __106645) (S_8 O_7)) c_106652
        end
      end
    end
  end
end

