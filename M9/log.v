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



Inductive Eq_0 (A_508121 : Type) (x_508122 : A_508121) : (A_508121) -> Type :=
| refl_1 (A_508124 : Type)
           (x_508125 : A_508124) : (Eq_0 A_508124 x_508125 x_508125).

Definition Eq_trans_508126 :=
  ((fun A_508127 x_508128 y_508129 z_508130 e1_508131 e2_508132 =>
      match e2_508132 in (Eq_0 __508134 __508135 y_508136) return
        (Eq_0 A_508127 x_508128 y_508136)
      with
      | (refl_1 ) => e1_508131
      end) :
    (A_508137 : Type) ->
      (x_508138 : A_508137) ->
        (y_508139 : A_508137) ->
          (z_508140 : A_508137) ->
            (e1_508141 : (Eq_0 A_508137 x_508138 y_508139)) ->
              (e2_508142 : (Eq_0 A_508137 y_508139 z_508140)) ->
                (Eq_0 A_508137 x_508138 z_508140)).

Definition Eq_sym_508143 :=
  ((fun A_508144 x_508145 y_508146 e_508147 =>
      match e_508147 in (Eq_0 __508149 __508150 y_508151) return
        (Eq_0 A_508144 y_508151 x_508145)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_508152 : Type) ->
      (x_508153 : A_508152) ->
        (y_508154 : A_508152) ->
          (e_508155 : (Eq_0 A_508152 x_508153 y_508154)) ->
            (Eq_0 A_508152 y_508154 x_508153)).

Definition TyInd_508156 :=
  ((fun A_508157 x_508158 y_508159 P_508160 e_508161 f_508162 =>
      match e_508161 in (Eq_0 __508164 __508165 y_508166) return
        (P_508160) y_508166
      with
      | (refl_1 ) => f_508162
      end) :
    (A_508167 : Type) ->
      (x_508168 : A_508167) ->
        (y_508169 : A_508167) ->
          (P_508170 : (A_508167) -> Type) ->
            (e_508172 : (Eq_0 A_508167 x_508168 y_508169)) ->
              (f_508173 : (P_508170) x_508168) -> (P_508170) y_508169).

Definition LnInd_508174 :=
  ((fun A_508175 x_508176 y_508177 P_508178 e_508179 f_508180 =>
      match e_508179 in (Eq_0 __508182 __508183 y_508184) return
        (P_508178) y_508184
      with
      | (refl_1 ) => f_508180
      end) :
    (A_508185 : Type) ->
      (x_508186 : A_508185) ->
        (y_508187 : A_508185) ->
          (P_508188 : (A_508185) -> Linear) ->
            (e_508190 : (Eq_0 A_508185 x_508186 y_508187)) ->
              (f_508191 : (P_508188) x_508186) -> (P_508188) y_508187).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_508193 :=
  ((fix add_508194 m_508195 n_508196 =>
      match m_508195 with
      | (O_7 ) => n_508196
      | (S_8 m_508197) => (S_8 ((add_508194) m_508197) n_508196)
      end) :
    (m_508198 : Nat_6) -> (n_508199 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_508200 : Type) (F_508201 : (A_508200) -> Type) : Type :=
| pair_13 (A_508203 : Type)
            (F_508204 : (A_508203) -> Type)
              : (x_508206 : A_508203) ->
                  ((F_508204) x_508206) -> (Sigma_12 A_508203 F_508204).

Inductive Tensor_14 (A_508208 : Linear) (B_508209 : Linear) : Linear :=
| tpair_15 (A_508210 : Linear)
             (B_508211 : Linear)
               : (A_508210) -> (B_508211) -> (Tensor_14 A_508210 B_508211).

Inductive FTensor_16 (A_508214 : Type)
                       (F_508215 : (A_508214) -> Linear) : Linear :=
| fpair_17 (A_508217 : Type)
             (F_508218 : (A_508217) -> Linear)
               : (x_508220 : A_508217) ->
                   ((F_508218) x_508220) -> (FTensor_16 A_508217 F_508218).

Axiom unsafeC_508222 : (A_508223 : Linear) -> (A_508223) -> Unit_2.

Axiom unsafeP_508225 : (A_508226 : Linear) -> A_508226.

Definition Loc_508227 := ((Nat_6) : Type).

Axiom PtsTo_508228 : (Loc_508227) -> (Type) -> Linear.

Definition Ptr_508231 :=
  ((fun A_508232 =>
      (FTensor_16
        Loc_508227 fun l_508233 => ((PtsTo_508228) l_508233) A_508232)) :
    (A_508234 : Type) -> Linear).

Axiom New_508235 : (A_508236 : Type) -> (A_508236) -> (Ptr_508231) A_508236.

Axiom Free_508238 : (A_508239 : Type) -> ((Ptr_508231) A_508239) -> Unit_2.

Axiom Get_508241 :
  (A_508242 : Type) ->
    (l_508243 : Loc_508227) ->
      (((PtsTo_508228) l_508243) A_508242) ->
        (FTensor_16
          A_508242 fun __508245 => ((PtsTo_508228) l_508243) A_508242).

Axiom Set_508246 :
  (A_508247 : Type) ->
    (B_508248 : Type) ->
      (B_508248) ->
        (l_508250 : Loc_508227) ->
          (((PtsTo_508228) l_508250) A_508247) ->
            ((PtsTo_508228) l_508250) B_508248.

Axiom ptsto_508252 : (A_508253 : Type) -> (Nat_6) -> (A_508253) -> Linear.

Axiom new_508256 :
  (A_508257 : Type) ->
    (x_508258 : A_508257) ->
      (FTensor_16
        Nat_6 fun l_508259 => (((ptsto_508252) A_508257) l_508259) x_508258).

Axiom free_508260 :
  (A_508261 : Type) ->
    (l_508262 : Nat_6) ->
      (x_508263 : A_508261) ->
        ((((ptsto_508252) A_508261) l_508262) x_508263) -> Unit_2.

Axiom get_508265 :
  (A_508266 : Type) ->
    (l_508267 : Nat_6) ->
      (x_508268 : A_508266) ->
        ((((ptsto_508252) A_508266) l_508267) x_508268) ->
          (FTensor_16
            (Sigma_12
              A_508266 fun y_508270 => (Eq_0 A_508266 x_508268 y_508270))
              fun __508271 => (((ptsto_508252) A_508266) l_508267) x_508268).

Axiom set_508272 :
  (A_508273 : Type) ->
    (B_508274 : Type) ->
      (l_508275 : Nat_6) ->
        (x_508276 : A_508273) ->
          ((((ptsto_508252) A_508273) l_508275) x_508276) ->
            (y_508278 : B_508274) ->
              (((ptsto_508252) B_508274) l_508275) y_508278.

Definition main_508279 :=
  ((let x_508280 := ((new_508256) Nat_6) (S_8 O_7) in
    match x_508280 with
    | (fpair_17 __508281 c_508282) =>
      let x_508283 := ((((get_508265) Nat_6) __508281) (S_8 O_7)) c_508282 in
      match x_508283 with
      | (fpair_17 xeq_508284 c_508285) =>
        let x_508286 := ((((get_508265) Nat_6) __508281) (S_8 O_7)) c_508285
        in
        match x_508286 with
        | (fpair_17 yeq_508287 c_508288) =>
          let x_508289 := xeq_508284 in
          match x_508289 with
          | (pair_13 x_508290 pf1_508291) =>
            let x0_508292 := yeq_508287 in
            match x0_508292 with
            | (pair_13 y_508293 pf2_508294) =>
              let pf1_508295 :=
                ((((Eq_sym_508143) Nat_6) (S_8 O_7)) x_508290) pf1_508291
              in
              let pf_508296 :=
                ((((((((Eq_trans_508126) Nat_6) x_508290) (S_8 O_7)) y_508293)
                     pf1_508295)
                    pf2_508294) :
                  (Eq_0 Nat_6 x_508290 y_508293))
              in
              let c_508297 :=
                ((((((set_508272) Nat_6) Nat_6) __508281) (S_8 O_7)) c_508288)
                  (S_8 (S_8 O_7))
              in
              let x0_508298 :=
                ((((get_508265) Nat_6) __508281) (S_8 (S_8 O_7))) c_508297
              in
              match x0_508298 with
              | (fpair_17 zeq_508299 c_508300) =>
                let x0_508301 := zeq_508299 in
                match x0_508301 with
                | (pair_13 z_508302 pf3_508303) =>
                  let pf_508304 :=
                    ((pf3_508303) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_508302))
                  in
                  ((((free_508260) Nat_6) __508281) (S_8 (S_8 O_7))) c_508300
                end
              end
            end
          end
        end
      end
    end) : Unit_2).



match ((new_26) Nat_6) (S_8 O_7) with
| (fpair_17 __508626 c_508627) =>
  let x_508628 := ((((get_28) Nat_6) __508626) (S_8 O_7)) c_508627 in
  match x_508628 with
  | (fpair_17 xeq_508629 c_508630) =>
    let x_508631 := ((((get_28) Nat_6) __508626) (S_8 O_7)) c_508630 in
    match x_508631 with
    | (fpair_17 yeq_508632 c_508633) =>
      let x_508634 := xeq_508629 in
      match x_508634 with
      | (pair_13 x_508635 pf1_508636) =>
        let x0_508637 := yeq_508632 in
        match x0_508637 with
        | (pair_13 y_508638 pf2_508639) =>
          let pf1_508640 :=
            ((((fun A_508641 x_508642 y_508643 e_508644 =>
                  match e_508644 in (Eq_0 __508646 __508647 y_508648) return
                    (Eq_0 A_508641 y_508648 x_508642)
                  with
                  | (refl_1 ) => refl_1
                  end)
                 Nat_6)
                (S_8 O_7))
               x_508635)
              pf1_508636
          in
          let pf_508649 :=
            ((((((((fun A_508650 x_508651 y_508652 z_508653 e1_508654 e2_508655 =>
                      match e2_508655 in (Eq_0 __508657 __508658 y_508659) return
                        (Eq_0 A_508650 x_508651 y_508659)
                      with
                      | (refl_1 ) => e1_508654
                      end)
                     Nat_6)
                    x_508635)
                   (S_8 O_7))
                  y_508638)
                 pf1_508640)
                pf2_508639) :
              (Eq_0 Nat_6 x_508635 y_508638))
          in
          let c_508660 :=
            ((((((set_29) Nat_6) Nat_6) __508626) (S_8 O_7)) c_508633)
              (S_8 (S_8 O_7))
          in
          let x0_508661 :=
            ((((get_28) Nat_6) __508626) (S_8 (S_8 O_7))) c_508660
          in
          match x0_508661 with
          | (fpair_17 zeq_508662 c_508663) =>
            let x0_508664 := zeq_508662 in
            match x0_508664 with
            | (pair_13 z_508665 pf3_508666) =>
              let pf_508667 :=
                ((pf3_508666) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_508665))
              in ((((free_27) Nat_6) __508626) (S_8 (S_8 O_7))) c_508663
            end
          end
        end
      end
    end
  end
end

