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
    in
    let c_134 := ((((((set_113) ?22) ?23) ?24) ?25) c_134) (S_8 (S_8 O_7)) in
    let (fpair_17 zeq_145 c_134) := ((((get_99) ?26) ?27) ?28) c_134 in
    let (pair_13 z_146 pf3_147) := zeq_145 in
    let pf_143 := ((pf3_147) : (Eq_0 ?29 (S_8 (S_8 O_7)) z_146)) in
    ((((free_86) ?30) ?31) ?32) c_134) : Unit_2).



Inductive Eq_0 (A_185 : Type) (x_186 : A_185) : (A_185) -> Type :=
| refl_1 (A_188 : Type) (x_189 : A_188) : (Eq_0 A_188 x_189 x_189).

Definition Eq_trans_190 :=
  ((fun A_191 x_192 y_193 z_194 e1_195 e2_196 =>
      match e2_196 in (Eq_0 __198 __199 y_200) return
        (Eq_0 A_191 x_192 y_200)
      with
      | (refl_1 ) => e1_195
      end) :
    (A_201 : Type) ->
      (x_202 : A_201) ->
        (y_203 : A_201) ->
          (z_204 : A_201) ->
            (e1_205 : (Eq_0 A_201 x_202 y_203)) ->
              (e2_206 : (Eq_0 A_201 y_203 z_204)) -> (Eq_0 A_201 x_202 z_204)).

Definition Eq_sym_207 :=
  ((fun A_208 x_209 y_210 e_211 =>
      match e_211 in (Eq_0 __213 __214 y_215) return (Eq_0 A_208 y_215 x_209)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_216 : Type) ->
      (x_217 : A_216) ->
        (y_218 : A_216) ->
          (e_219 : (Eq_0 A_216 x_217 y_218)) -> (Eq_0 A_216 y_218 x_217)).

Definition TyInd_220 :=
  ((fun A_221 x_222 y_223 P_224 e_225 f_226 =>
      match e_225 in (Eq_0 __228 __229 y_230) return (P_224) y_230 with
      | (refl_1 ) => f_226
      end) :
    (A_231 : Type) ->
      (x_232 : A_231) ->
        (y_233 : A_231) ->
          (P_234 : (A_231) -> Type) ->
            (e_236 : (Eq_0 A_231 x_232 y_233)) ->
              (f_237 : (P_234) x_232) -> (P_234) y_233).

Definition LnInd_238 :=
  ((fun A_239 x_240 y_241 P_242 e_243 f_244 =>
      match e_243 in (Eq_0 __246 __247 y_248) return (P_242) y_248 with
      | (refl_1 ) => f_244
      end) :
    (A_249 : Type) ->
      (x_250 : A_249) ->
        (y_251 : A_249) ->
          (P_252 : (A_249) -> Linear) ->
            (e_254 : (Eq_0 A_249 x_250 y_251)) ->
              (f_255 : (P_252) x_250) -> (P_252) y_251).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_257 :=
  ((fix add_258 m_259 n_260 =>
      match m_259 with
      | (O_7 ) => n_260
      | (S_8 m_261) => (S_8 ((add_258) m_261) n_260)
      end) :
    (m_262 : Nat_6) -> (n_263 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_264 : Type) (F_265 : (A_264) -> Type) : Type :=
| pair_13 (A_267 : Type)
            (F_268 : (A_267) -> Type)
              : (x_270 : A_267) -> ((F_268) x_270) -> (Sigma_12 A_267 F_268).

Inductive Tensor_14 (A_272 : Linear) (B_273 : Linear) : Linear :=
| tpair_15 (A_274 : Linear)
             (B_275 : Linear) : (A_274) -> (B_275) -> (Tensor_14 A_274 B_275).

Inductive FTensor_16 (A_278 : Type) (F_279 : (A_278) -> Linear) : Linear :=
| fpair_17 (A_281 : Type)
             (F_282 : (A_281) -> Linear)
               : (x_284 : A_281) ->
                   ((F_282) x_284) -> (FTensor_16 A_281 F_282).

Axiom unsafeC_286 : (A_287 : Linear) -> (A_287) -> Unit_2.

Axiom unsafeP_289 : (A_290 : Linear) -> A_290.

Definition Loc_291 := ((Nat_6) : Type).

Axiom PtsTo_292 : (Loc_291) -> (Type) -> Linear.

Definition Ptr_295 :=
  ((fun A_296 => (FTensor_16 Loc_291 fun l_297 => ((PtsTo_292) l_297) A_296)) :
    (A_298 : Type) -> Linear).

Axiom New_299 : (A_300 : Type) -> (A_300) -> (Ptr_295) A_300.

Axiom Free_302 : (A_303 : Type) -> ((Ptr_295) A_303) -> Unit_2.

Axiom Get_305 :
  (A_306 : Type) ->
    (l_307 : Loc_291) ->
      (((PtsTo_292) l_307) A_306) ->
        (FTensor_16 A_306 fun __309 => ((PtsTo_292) l_307) A_306).

Axiom Set_310 :
  (A_311 : Type) ->
    (B_312 : Type) ->
      (B_312) ->
        (l_314 : Loc_291) ->
          (((PtsTo_292) l_314) A_311) -> ((PtsTo_292) l_314) B_312.

Axiom ptsto_316 : (A_317 : Type) -> (Nat_6) -> (A_317) -> Linear.

Axiom new_320 :
  (A_321 : Type) ->
    (x_322 : A_321) ->
      (FTensor_16
        Nat_6
          fun l_323 =>
            (((ptsto_316)
                ((((((((((((((((((?0) Eq_trans_190) Eq_sym_207) TyInd_220)
                                LnInd_238)
                               add_257)
                              unsafeC_286)
                             unsafeP_289)
                            Loc_291)
                           PtsTo_292)
                          Ptr_295)
                         New_299)
                        Free_302)
                       Get_305)
                      Set_310)
                     ptsto_316)
                    A_321)
                   x_322)
                  l_323)
               l_323)
              x_322).

Axiom free_324 :
  (A_325 : Type) ->
    (l_326 : Nat_6) ->
      (x_327 : A_325) ->
        ((((ptsto_316)
             (((((((((((((((((((?1) Eq_trans_190) Eq_sym_207) TyInd_220)
                              LnInd_238)
                             add_257)
                            unsafeC_286)
                           unsafeP_289)
                          Loc_291)
                         PtsTo_292)
                        Ptr_295)
                       New_299)
                      Free_302)
                     Get_305)
                    Set_310)
                   ptsto_316)
                  new_320)
                 A_325)
                l_326)
               x_327)
            l_326)
           x_327) ->
          Unit_2.

Axiom get_329 :
  (A_330 : Type) ->
    (l_331 : Nat_6) ->
      (x_332 : A_330) ->
        ((((ptsto_316)
             ((((((((((((((((((((?2) Eq_trans_190) Eq_sym_207) TyInd_220)
                               LnInd_238)
                              add_257)
                             unsafeC_286)
                            unsafeP_289)
                           Loc_291)
                          PtsTo_292)
                         Ptr_295)
                        New_299)
                       Free_302)
                      Get_305)
                     Set_310)
                    ptsto_316)
                   new_320)
                  free_324)
                 A_330)
                l_331)
               x_332)
            l_331)
           x_332) ->
          (FTensor_16
            (Sigma_12
              A_330
                fun y_334 =>
                  (Eq_0
                    ((((((((((((((((((((((?3) __333) Eq_trans_190) Eq_sym_207)
                                        TyInd_220)
                                       LnInd_238)
                                      add_257)
                                     unsafeC_286)
                                    unsafeP_289)
                                   Loc_291)
                                  PtsTo_292)
                                 Ptr_295)
                                New_299)
                               Free_302)
                              Get_305)
                             Set_310)
                            ptsto_316)
                           new_320)
                          free_324)
                         A_330)
                        l_331)
                       x_332)
                      y_334 x_332 y_334))
              fun __335 =>
                (((ptsto_316)
                    (((((((((((((((((((((?4) __335) Eq_trans_190) Eq_sym_207)
                                       TyInd_220)
                                      LnInd_238)
                                     add_257)
                                    unsafeC_286)
                                   unsafeP_289)
                                  Loc_291)
                                 PtsTo_292)
                                Ptr_295)
                               New_299)
                              Free_302)
                             Get_305)
                            Set_310)
                           ptsto_316)
                          new_320)
                         free_324)
                        A_330)
                       l_331)
                      x_332)
                   l_331)
                  x_332).

Axiom set_336 :
  (A_337 : Type) ->
    (B_338 : Type) ->
      (l_339 : Nat_6) ->
        (x_340 : A_337) ->
          ((((ptsto_316)
               ((((((((((((((((((((((?5) Eq_trans_190) Eq_sym_207) TyInd_220)
                                   LnInd_238)
                                  add_257)
                                 unsafeC_286)
                                unsafeP_289)
                               Loc_291)
                              PtsTo_292)
                             Ptr_295)
                            New_299)
                           Free_302)
                          Get_305)
                         Set_310)
                        ptsto_316)
                       new_320)
                      free_324)
                     get_329)
                    A_337)
                   B_338)
                  l_339)
                 x_340)
              l_339)
             x_340) ->
            (y_342 : B_338) ->
              (((ptsto_316)
                  ((((((((((((((((((((((((?6) __341) Eq_trans_190) Eq_sym_207)
                                        TyInd_220)
                                       LnInd_238)
                                      add_257)
                                     unsafeC_286)
                                    unsafeP_289)
                                   Loc_291)
                                  PtsTo_292)
                                 Ptr_295)
                                New_299)
                               Free_302)
                              Get_305)
                             Set_310)
                            ptsto_316)
                           new_320)
                          free_324)
                         get_329)
                        A_337)
                       B_338)
                      l_339)
                     x_340)
                    y_342)
                 l_339)
                y_342.

Definition main_343 :=
  ((let x_344 :=
      ((new_320)
         (((((((((((((((((((?7) Eq_trans_190) Eq_sym_207) TyInd_220)
                          LnInd_238)
                         add_257)
                        unsafeC_286)
                       unsafeP_289)
                      Loc_291)
                     PtsTo_292)
                    Ptr_295)
                   New_299)
                  Free_302)
                 Get_305)
                Set_310)
               ptsto_316)
              new_320)
             free_324)
            get_329)
           set_336)
        (S_8 O_7)
    in
    match x_344 with
    | (fpair_17 __345 c_346) =>
      let x_347 :=
        ((((get_329)
             (((((((((((((((((((((?8) __345) Eq_trans_190) Eq_sym_207)
                                TyInd_220)
                               LnInd_238)
                              add_257)
                             unsafeC_286)
                            unsafeP_289)
                           Loc_291)
                          PtsTo_292)
                         Ptr_295)
                        New_299)
                       Free_302)
                      Get_305)
                     Set_310)
                    ptsto_316)
                   new_320)
                  free_324)
                 get_329)
                set_336)
               c_346)
            (((((((((((((((((((((?9) __345) Eq_trans_190) Eq_sym_207)
                               TyInd_220)
                              LnInd_238)
                             add_257)
                            unsafeC_286)
                           unsafeP_289)
                          Loc_291)
                         PtsTo_292)
                        Ptr_295)
                       New_299)
                      Free_302)
                     Get_305)
                    Set_310)
                   ptsto_316)
                  new_320)
                 free_324)
                get_329)
               set_336)
              c_346)
           (((((((((((((((((((((?10) __345) Eq_trans_190) Eq_sym_207)
                              TyInd_220)
                             LnInd_238)
                            add_257)
                           unsafeC_286)
                          unsafeP_289)
                         Loc_291)
                        PtsTo_292)
                       Ptr_295)
                      New_299)
                     Free_302)
                    Get_305)
                   Set_310)
                  ptsto_316)
                 new_320)
                free_324)
               get_329)
              set_336)
             c_346)
          c_346
      in
      match x_347 with
      | (fpair_17 xeq_348 c_349) =>
        let x_350 :=
          ((((get_329)
               ((((((((((((((((((((((?11) __345) Eq_trans_190) Eq_sym_207)
                                   TyInd_220)
                                  LnInd_238)
                                 add_257)
                                unsafeC_286)
                               unsafeP_289)
                              Loc_291)
                             PtsTo_292)
                            Ptr_295)
                           New_299)
                          Free_302)
                         Get_305)
                        Set_310)
                       ptsto_316)
                      new_320)
                     free_324)
                    get_329)
                   set_336)
                  c_349)
                 xeq_348)
              ((((((((((((((((((((((?12) __345) Eq_trans_190) Eq_sym_207)
                                  TyInd_220)
                                 LnInd_238)
                                add_257)
                               unsafeC_286)
                              unsafeP_289)
                             Loc_291)
                            PtsTo_292)
                           Ptr_295)
                          New_299)
                         Free_302)
                        Get_305)
                       Set_310)
                      ptsto_316)
                     new_320)
                    free_324)
                   get_329)
                  set_336)
                 c_349)
                xeq_348)
             ((((((((((((((((((((((?13) __345) Eq_trans_190) Eq_sym_207)
                                 TyInd_220)
                                LnInd_238)
                               add_257)
                              unsafeC_286)
                             unsafeP_289)
                            Loc_291)
                           PtsTo_292)
                          Ptr_295)
                         New_299)
                        Free_302)
                       Get_305)
                      Set_310)
                     ptsto_316)
                    new_320)
                   free_324)
                  get_329)
                 set_336)
                c_349)
               xeq_348)
            c_349
        in
        match x_350 with
        | (fpair_17 yeq_351 c_352) =>
          let x_353 := xeq_348 in
          match x_353 with
          | (pair_13 x_354 pf1_355) =>
            let x0_356 := yeq_351 in
            match x0_356 with
            | (pair_13 y_357 pf2_358) =>
              let pf1_359 :=
                ((((Eq_sym_207)
                     (((((((((((((((((((((((((((?14) __345) Eq_trans_190)
                                               Eq_sym_207)
                                              TyInd_220)
                                             LnInd_238)
                                            add_257)
                                           unsafeC_286)
                                          unsafeP_289)
                                         Loc_291)
                                        PtsTo_292)
                                       Ptr_295)
                                      New_299)
                                     Free_302)
                                    Get_305)
                                   Set_310)
                                  ptsto_316)
                                 new_320)
                                free_324)
                               get_329)
                              set_336)
                             c_352)
                            xeq_348)
                           yeq_351)
                          x_354)
                         pf1_355)
                        y_357)
                       pf2_358)
                    (((((((((((((((((((((((((((?15) __345) Eq_trans_190)
                                              Eq_sym_207)
                                             TyInd_220)
                                            LnInd_238)
                                           add_257)
                                          unsafeC_286)
                                         unsafeP_289)
                                        Loc_291)
                                       PtsTo_292)
                                      Ptr_295)
                                     New_299)
                                    Free_302)
                                   Get_305)
                                  Set_310)
                                 ptsto_316)
                                new_320)
                               free_324)
                              get_329)
                             set_336)
                            c_352)
                           xeq_348)
                          yeq_351)
                         x_354)
                        pf1_355)
                       y_357)
                      pf2_358)
                   (((((((((((((((((((((((((((?16) __345) Eq_trans_190)
                                             Eq_sym_207)
                                            TyInd_220)
                                           LnInd_238)
                                          add_257)
                                         unsafeC_286)
                                        unsafeP_289)
                                       Loc_291)
                                      PtsTo_292)
                                     Ptr_295)
                                    New_299)
                                   Free_302)
                                  Get_305)
                                 Set_310)
                                ptsto_316)
                               new_320)
                              free_324)
                             get_329)
                            set_336)
                           c_352)
                          xeq_348)
                         yeq_351)
                        x_354)
                       pf1_355)
                      y_357)
                     pf2_358)
                  pf1_355
              in
              let pf_360 :=
                ((((((((Eq_trans_190)
                         (((((((((((((((((((((((((((?18) __345) Eq_trans_190)
                                                   Eq_sym_207)
                                                  TyInd_220)
                                                 LnInd_238)
                                                add_257)
                                               unsafeC_286)
                                              unsafeP_289)
                                             Loc_291)
                                            PtsTo_292)
                                           Ptr_295)
                                          New_299)
                                         Free_302)
                                        Get_305)
                                       Set_310)
                                      ptsto_316)
                                     new_320)
                                    free_324)
                                   get_329)
                                  set_336)
                                 c_352)
                                xeq_348)
                               yeq_351)
                              x_354)
                             pf1_359)
                            y_357)
                           pf2_358)
                        (((((((((((((((((((((((((((?19) __345) Eq_trans_190)
                                                  Eq_sym_207)
                                                 TyInd_220)
                                                LnInd_238)
                                               add_257)
                                              unsafeC_286)
                                             unsafeP_289)
                                            Loc_291)
                                           PtsTo_292)
                                          Ptr_295)
                                         New_299)
                                        Free_302)
                                       Get_305)
                                      Set_310)
                                     ptsto_316)
                                    new_320)
                                   free_324)
                                  get_329)
                                 set_336)
                                c_352)
                               xeq_348)
                              yeq_351)
                             x_354)
                            pf1_359)
                           y_357)
                          pf2_358)
                       (((((((((((((((((((((((((((?20) __345) Eq_trans_190)
                                                 Eq_sym_207)
                                                TyInd_220)
                                               LnInd_238)
                                              add_257)
                                             unsafeC_286)
                                            unsafeP_289)
                                           Loc_291)
                                          PtsTo_292)
                                         Ptr_295)
                                        New_299)
                                       Free_302)
                                      Get_305)
                                     Set_310)
                                    ptsto_316)
                                   new_320)
                                  free_324)
                                 get_329)
                                set_336)
                               c_352)
                              xeq_348)
                             yeq_351)
                            x_354)
                           pf1_359)
                          y_357)
                         pf2_358)
                      (((((((((((((((((((((((((((?21) __345) Eq_trans_190)
                                                Eq_sym_207)
                                               TyInd_220)
                                              LnInd_238)
                                             add_257)
                                            unsafeC_286)
                                           unsafeP_289)
                                          Loc_291)
                                         PtsTo_292)
                                        Ptr_295)
                                       New_299)
                                      Free_302)
                                     Get_305)
                                    Set_310)
                                   ptsto_316)
                                  new_320)
                                 free_324)
                                get_329)
                               set_336)
                              c_352)
                             xeq_348)
                            yeq_351)
                           x_354)
                          pf1_359)
                         y_357)
                        pf2_358)
                     pf1_359)
                    pf2_358) :
                  (Eq_0
                    (((((((((((((((((((((((((((?17) __345) Eq_trans_190)
                                              Eq_sym_207)
                                             TyInd_220)
                                            LnInd_238)
                                           add_257)
                                          unsafeC_286)
                                         unsafeP_289)
                                        Loc_291)
                                       PtsTo_292)
                                      Ptr_295)
                                     New_299)
                                    Free_302)
                                   Get_305)
                                  Set_310)
                                 ptsto_316)
                                new_320)
                               free_324)
                              get_329)
                             set_336)
                            c_352)
                           xeq_348)
                          yeq_351)
                         x_354)
                        pf1_359)
                       y_357)
                      pf2_358 x_354 y_357))
              in
              let c_361 :=
                ((((((set_336)
                       ((((((((((((((((((((((((((((?22) __345) Eq_trans_190)
                                                  Eq_sym_207)
                                                 TyInd_220)
                                                LnInd_238)
                                               add_257)
                                              unsafeC_286)
                                             unsafeP_289)
                                            Loc_291)
                                           PtsTo_292)
                                          Ptr_295)
                                         New_299)
                                        Free_302)
                                       Get_305)
                                      Set_310)
                                     ptsto_316)
                                    new_320)
                                   free_324)
                                  get_329)
                                 set_336)
                                c_352)
                               xeq_348)
                              yeq_351)
                             x_354)
                            pf1_359)
                           y_357)
                          pf2_358)
                         pf_360)
                      ((((((((((((((((((((((((((((?23) __345) Eq_trans_190)
                                                 Eq_sym_207)
                                                TyInd_220)
                                               LnInd_238)
                                              add_257)
                                             unsafeC_286)
                                            unsafeP_289)
                                           Loc_291)
                                          PtsTo_292)
                                         Ptr_295)
                                        New_299)
                                       Free_302)
                                      Get_305)
                                     Set_310)
                                    ptsto_316)
                                   new_320)
                                  free_324)
                                 get_329)
                                set_336)
                               c_352)
                              xeq_348)
                             yeq_351)
                            x_354)
                           pf1_359)
                          y_357)
                         pf2_358)
                        pf_360)
                     ((((((((((((((((((((((((((((?24) __345) Eq_trans_190)
                                                Eq_sym_207)
                                               TyInd_220)
                                              LnInd_238)
                                             add_257)
                                            unsafeC_286)
                                           unsafeP_289)
                                          Loc_291)
                                         PtsTo_292)
                                        Ptr_295)
                                       New_299)
                                      Free_302)
                                     Get_305)
                                    Set_310)
                                   ptsto_316)
                                  new_320)
                                 free_324)
                                get_329)
                               set_336)
                              c_352)
                             xeq_348)
                            yeq_351)
                           x_354)
                          pf1_359)
                         y_357)
                        pf2_358)
                       pf_360)
                    ((((((((((((((((((((((((((((?25) __345) Eq_trans_190)
                                               Eq_sym_207)
                                              TyInd_220)
                                             LnInd_238)
                                            add_257)
                                           unsafeC_286)
                                          unsafeP_289)
                                         Loc_291)
                                        PtsTo_292)
                                       Ptr_295)
                                      New_299)
                                     Free_302)
                                    Get_305)
                                   Set_310)
                                  ptsto_316)
                                 new_320)
                                free_324)
                               get_329)
                              set_336)
                             c_352)
                            xeq_348)
                           yeq_351)
                          x_354)
                         pf1_359)
                        y_357)
                       pf2_358)
                      pf_360)
                   c_352)
                  (S_8 (S_8 O_7))
              in
              let x0_362 :=
                ((((get_329)
                     ((((((((((((((((((((((((((((?26) __345) Eq_trans_190)
                                                Eq_sym_207)
                                               TyInd_220)
                                              LnInd_238)
                                             add_257)
                                            unsafeC_286)
                                           unsafeP_289)
                                          Loc_291)
                                         PtsTo_292)
                                        Ptr_295)
                                       New_299)
                                      Free_302)
                                     Get_305)
                                    Set_310)
                                   ptsto_316)
                                  new_320)
                                 free_324)
                                get_329)
                               set_336)
                              c_361)
                             xeq_348)
                            yeq_351)
                           x_354)
                          pf1_359)
                         y_357)
                        pf2_358)
                       pf_360)
                    ((((((((((((((((((((((((((((?27) __345) Eq_trans_190)
                                               Eq_sym_207)
                                              TyInd_220)
                                             LnInd_238)
                                            add_257)
                                           unsafeC_286)
                                          unsafeP_289)
                                         Loc_291)
                                        PtsTo_292)
                                       Ptr_295)
                                      New_299)
                                     Free_302)
                                    Get_305)
                                   Set_310)
                                  ptsto_316)
                                 new_320)
                                free_324)
                               get_329)
                              set_336)
                             c_361)
                            xeq_348)
                           yeq_351)
                          x_354)
                         pf1_359)
                        y_357)
                       pf2_358)
                      pf_360)
                   ((((((((((((((((((((((((((((?28) __345) Eq_trans_190)
                                              Eq_sym_207)
                                             TyInd_220)
                                            LnInd_238)
                                           add_257)
                                          unsafeC_286)
                                         unsafeP_289)
                                        Loc_291)
                                       PtsTo_292)
                                      Ptr_295)
                                     New_299)
                                    Free_302)
                                   Get_305)
                                  Set_310)
                                 ptsto_316)
                                new_320)
                               free_324)
                              get_329)
                             set_336)
                            c_361)
                           xeq_348)
                          yeq_351)
                         x_354)
                        pf1_359)
                       y_357)
                      pf2_358)
                     pf_360)
                  c_361
              in
              match x0_362 with
              | (fpair_17 zeq_363 c_364) =>
                let x0_365 := zeq_363 in
                match x0_365 with
                | (pair_13 z_366 pf3_367) =>
                  let pf_368 :=
                    ((pf3_367) :
                      (Eq_0
                        (((((((((((((((((((((((((((((((?29) __345)
                                                       Eq_trans_190)
                                                      Eq_sym_207)
                                                     TyInd_220)
                                                    LnInd_238)
                                                   add_257)
                                                  unsafeC_286)
                                                 unsafeP_289)
                                                Loc_291)
                                               PtsTo_292)
                                              Ptr_295)
                                             New_299)
                                            Free_302)
                                           Get_305)
                                          Set_310)
                                         ptsto_316)
                                        new_320)
                                       free_324)
                                      get_329)
                                     set_336)
                                    c_364)
                                   xeq_348)
                                  yeq_351)
                                 x_354)
                                pf1_359)
                               y_357)
                              pf2_358)
                             pf_360)
                            zeq_363)
                           z_366)
                          pf3_367 (S_8 (S_8 O_7)) z_366))
                  in
                  ((((free_324)
                       (((((((((((((((((((((((((((((((?30) __345)
                                                      Eq_trans_190)
                                                     Eq_sym_207)
                                                    TyInd_220)
                                                   LnInd_238)
                                                  add_257)
                                                 unsafeC_286)
                                                unsafeP_289)
                                               Loc_291)
                                              PtsTo_292)
                                             Ptr_295)
                                            New_299)
                                           Free_302)
                                          Get_305)
                                         Set_310)
                                        ptsto_316)
                                       new_320)
                                      free_324)
                                     get_329)
                                    set_336)
                                   c_364)
                                  xeq_348)
                                 yeq_351)
                                x_354)
                               pf1_359)
                              y_357)
                             pf2_358)
                            pf_368)
                           zeq_363)
                          z_366)
                         pf3_367)
                      (((((((((((((((((((((((((((((((?31) __345) Eq_trans_190)
                                                    Eq_sym_207)
                                                   TyInd_220)
                                                  LnInd_238)
                                                 add_257)
                                                unsafeC_286)
                                               unsafeP_289)
                                              Loc_291)
                                             PtsTo_292)
                                            Ptr_295)
                                           New_299)
                                          Free_302)
                                         Get_305)
                                        Set_310)
                                       ptsto_316)
                                      new_320)
                                     free_324)
                                    get_329)
                                   set_336)
                                  c_364)
                                 xeq_348)
                                yeq_351)
                               x_354)
                              pf1_359)
                             y_357)
                            pf2_358)
                           pf_368)
                          zeq_363)
                         z_366)
                        pf3_367)
                     (((((((((((((((((((((((((((((((?32) __345) Eq_trans_190)
                                                   Eq_sym_207)
                                                  TyInd_220)
                                                 LnInd_238)
                                                add_257)
                                               unsafeC_286)
                                              unsafeP_289)
                                             Loc_291)
                                            PtsTo_292)
                                           Ptr_295)
                                          New_299)
                                         Free_302)
                                        Get_305)
                                       Set_310)
                                      ptsto_316)
                                     new_320)
                                    free_324)
                                   get_329)
                                  set_336)
                                 c_364)
                                xeq_348)
                               yeq_351)
                              x_354)
                             pf1_359)
                            y_357)
                           pf2_358)
                          pf_368)
                         zeq_363)
                        z_366)
                       pf3_367)
                    c_364
                end
              end
            end
          end
        end
      end
    end) : Unit_2).



Inductive Eq_0 (A_87765 : Type) (x_87766 : A_87765) : (A_87765) -> Type :=
| refl_1 (A_87768 : Type)
           (x_87769 : A_87768) : (Eq_0 A_87768 x_87769 x_87769).

Definition Eq_trans_87770 :=
  ((fun A_87771 x_87772 y_87773 z_87774 e1_87775 e2_87776 =>
      match e2_87776 in (Eq_0 __87778 __87779 y_87780) return
        (Eq_0 A_87771 x_87772 y_87780)
      with
      | (refl_1 ) => e1_87775
      end) :
    (A_87781 : Type) ->
      (x_87782 : A_87781) ->
        (y_87783 : A_87781) ->
          (z_87784 : A_87781) ->
            (e1_87785 : (Eq_0 A_87781 x_87782 y_87783)) ->
              (e2_87786 : (Eq_0 A_87781 y_87783 z_87784)) ->
                (Eq_0 A_87781 x_87782 z_87784)).

Definition Eq_sym_87787 :=
  ((fun A_87788 x_87789 y_87790 e_87791 =>
      match e_87791 in (Eq_0 __87793 __87794 y_87795) return
        (Eq_0 A_87788 y_87795 x_87789)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_87796 : Type) ->
      (x_87797 : A_87796) ->
        (y_87798 : A_87796) ->
          (e_87799 : (Eq_0 A_87796 x_87797 y_87798)) ->
            (Eq_0 A_87796 y_87798 x_87797)).

Definition TyInd_87800 :=
  ((fun A_87801 x_87802 y_87803 P_87804 e_87805 f_87806 =>
      match e_87805 in (Eq_0 __87808 __87809 y_87810) return
        (P_87804) y_87810
      with
      | (refl_1 ) => f_87806
      end) :
    (A_87811 : Type) ->
      (x_87812 : A_87811) ->
        (y_87813 : A_87811) ->
          (P_87814 : (A_87811) -> Type) ->
            (e_87816 : (Eq_0 A_87811 x_87812 y_87813)) ->
              (f_87817 : (P_87814) x_87812) -> (P_87814) y_87813).

Definition LnInd_87818 :=
  ((fun A_87819 x_87820 y_87821 P_87822 e_87823 f_87824 =>
      match e_87823 in (Eq_0 __87826 __87827 y_87828) return
        (P_87822) y_87828
      with
      | (refl_1 ) => f_87824
      end) :
    (A_87829 : Type) ->
      (x_87830 : A_87829) ->
        (y_87831 : A_87829) ->
          (P_87832 : (A_87829) -> Linear) ->
            (e_87834 : (Eq_0 A_87829 x_87830 y_87831)) ->
              (f_87835 : (P_87832) x_87830) -> (P_87832) y_87831).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_87837 :=
  ((fix add_87838 m_87839 n_87840 =>
      match m_87839 with
      | (O_7 ) => n_87840
      | (S_8 m_87841) => (S_8 ((add_87838) m_87841) n_87840)
      end) :
    (m_87842 : Nat_6) -> (n_87843 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_87844 : Type) (F_87845 : (A_87844) -> Type) : Type :=
| pair_13 (A_87847 : Type)
            (F_87848 : (A_87847) -> Type)
              : (x_87850 : A_87847) ->
                  ((F_87848) x_87850) -> (Sigma_12 A_87847 F_87848).

Inductive Tensor_14 (A_87852 : Linear) (B_87853 : Linear) : Linear :=
| tpair_15 (A_87854 : Linear)
             (B_87855 : Linear)
               : (A_87854) -> (B_87855) -> (Tensor_14 A_87854 B_87855).

Inductive FTensor_16 (A_87858 : Type)
                       (F_87859 : (A_87858) -> Linear) : Linear :=
| fpair_17 (A_87861 : Type)
             (F_87862 : (A_87861) -> Linear)
               : (x_87864 : A_87861) ->
                   ((F_87862) x_87864) -> (FTensor_16 A_87861 F_87862).

Axiom unsafeC_87866 : (A_87867 : Linear) -> (A_87867) -> Unit_2.

Axiom unsafeP_87869 : (A_87870 : Linear) -> A_87870.

Definition Loc_87871 := ((Nat_6) : Type).

Axiom PtsTo_87872 : (Loc_87871) -> (Type) -> Linear.

Definition Ptr_87875 :=
  ((fun A_87876 =>
      (FTensor_16 Loc_87871 fun l_87877 => ((PtsTo_87872) l_87877) A_87876)) :
    (A_87878 : Type) -> Linear).

Axiom New_87879 : (A_87880 : Type) -> (A_87880) -> (Ptr_87875) A_87880.

Axiom Free_87882 : (A_87883 : Type) -> ((Ptr_87875) A_87883) -> Unit_2.

Axiom Get_87885 :
  (A_87886 : Type) ->
    (l_87887 : Loc_87871) ->
      (((PtsTo_87872) l_87887) A_87886) ->
        (FTensor_16 A_87886 fun __87889 => ((PtsTo_87872) l_87887) A_87886).

Axiom Set_87890 :
  (A_87891 : Type) ->
    (B_87892 : Type) ->
      (B_87892) ->
        (l_87894 : Loc_87871) ->
          (((PtsTo_87872) l_87894) A_87891) ->
            ((PtsTo_87872) l_87894) B_87892.

Axiom ptsto_87896 : (A_87897 : Type) -> (Nat_6) -> (A_87897) -> Linear.

Axiom new_87900 :
  (A_87901 : Type) ->
    (x_87902 : A_87901) ->
      (FTensor_16
        Nat_6 fun l_87903 => (((ptsto_87896) A_87901) l_87903) x_87902).

Axiom free_87904 :
  (A_87905 : Type) ->
    (l_87906 : Nat_6) ->
      (x_87907 : A_87905) ->
        ((((ptsto_87896) A_87905) l_87906) x_87907) -> Unit_2.

Axiom get_87909 :
  (A_87910 : Type) ->
    (l_87911 : Nat_6) ->
      (x_87912 : A_87910) ->
        ((((ptsto_87896) A_87910) l_87911) x_87912) ->
          (FTensor_16
            (Sigma_12 A_87910 fun y_87914 => (Eq_0 A_87910 x_87912 y_87914))
              fun __87915 => (((ptsto_87896) A_87910) l_87911) x_87912).

Axiom set_87916 :
  (A_87917 : Type) ->
    (B_87918 : Type) ->
      (l_87919 : Nat_6) ->
        (x_87920 : A_87917) ->
          ((((ptsto_87896) A_87917) l_87919) x_87920) ->
            (y_87922 : B_87918) -> (((ptsto_87896) B_87918) l_87919) y_87922.

Definition main_87923 :=
  ((let x_87924 := ((new_87900) Nat_6) (S_8 O_7) in
    match x_87924 with
    | (fpair_17 __87925 c_87926) =>
      let x_87927 := ((((get_87909) Nat_6) __87925) (S_8 O_7)) c_87926 in
      match x_87927 with
      | (fpair_17 xeq_87928 c_87929) =>
        let x_87930 := ((((get_87909) Nat_6) __87925) (S_8 O_7)) c_87929 in
        match x_87930 with
        | (fpair_17 yeq_87931 c_87932) =>
          let x_87933 := xeq_87928 in
          match x_87933 with
          | (pair_13 x_87934 pf1_87935) =>
            let x0_87936 := yeq_87931 in
            match x0_87936 with
            | (pair_13 y_87937 pf2_87938) =>
              let pf1_87939 :=
                ((((Eq_sym_87787) Nat_6) (S_8 O_7)) x_87934) pf1_87935
              in
              let pf_87940 :=
                ((((((((Eq_trans_87770) Nat_6) x_87934) (S_8 O_7)) y_87937)
                     pf1_87939)
                    pf2_87938) :
                  (Eq_0 Nat_6 x_87934 y_87937))
              in
              let c_87941 :=
                ((((((set_87916) Nat_6) Nat_6) __87925) (S_8 O_7)) c_87932)
                  (S_8 (S_8 O_7))
              in
              let x0_87942 :=
                ((((get_87909) Nat_6) __87925) (S_8 (S_8 O_7))) c_87941
              in
              match x0_87942 with
              | (fpair_17 zeq_87943 c_87944) =>
                let x0_87945 := zeq_87943 in
                match x0_87945 with
                | (pair_13 z_87946 pf3_87947) =>
                  let pf_87948 :=
                    ((pf3_87947) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_87946))
                  in ((((free_87904) Nat_6) __87925) (S_8 (S_8 O_7))) c_87944
                end
              end
            end
          end
        end
      end
    end) : Unit_2).



match ((new_26) Nat_6) (S_8 O_7) with
| (fpair_17 __88270 c_88271) =>
  let x_88272 := ((((get_28) Nat_6) __88270) (S_8 O_7)) c_88271 in
  match x_88272 with
  | (fpair_17 xeq_88273 c_88274) =>
    let x_88275 := ((((get_28) Nat_6) __88270) (S_8 O_7)) c_88274 in
    match x_88275 with
    | (fpair_17 yeq_88276 c_88277) =>
      let x_88278 := xeq_88273 in
      match x_88278 with
      | (pair_13 x_88279 pf1_88280) =>
        let x0_88281 := yeq_88276 in
        match x0_88281 with
        | (pair_13 y_88282 pf2_88283) =>
          let pf1_88284 :=
            ((((fun A_88285 x_88286 y_88287 e_88288 =>
                  match e_88288 in (Eq_0 __88290 __88291 y_88292) return
                    (Eq_0 A_88285 y_88292 x_88286)
                  with
                  | (refl_1 ) => refl_1
                  end)
                 Nat_6)
                (S_8 O_7))
               x_88279)
              pf1_88280
          in
          let pf_88293 :=
            ((((((((fun A_88294 x_88295 y_88296 z_88297 e1_88298 e2_88299 =>
                      match e2_88299 in (Eq_0 __88301 __88302 y_88303) return
                        (Eq_0 A_88294 x_88295 y_88303)
                      with
                      | (refl_1 ) => e1_88298
                      end)
                     Nat_6)
                    x_88279)
                   (S_8 O_7))
                  y_88282)
                 pf1_88284)
                pf2_88283) :
              (Eq_0 Nat_6 x_88279 y_88282))
          in
          let c_88304 :=
            ((((((set_29) Nat_6) Nat_6) __88270) (S_8 O_7)) c_88277)
              (S_8 (S_8 O_7))
          in
          let x0_88305 :=
            ((((get_28) Nat_6) __88270) (S_8 (S_8 O_7))) c_88304
          in
          match x0_88305 with
          | (fpair_17 zeq_88306 c_88307) =>
            let x0_88308 := zeq_88306 in
            match x0_88308 with
            | (pair_13 z_88309 pf3_88310) =>
              let pf_88311 :=
                ((pf3_88310) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_88309))
              in ((((free_27) Nat_6) __88270) (S_8 (S_8 O_7))) c_88307
            end
          end
        end
      end
    end
  end
end

