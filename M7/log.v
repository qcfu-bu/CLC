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

Definition Loc_42 := ((Nat_6) : Type).

Axiom PtsTo_43 : Loc_42 -> Type -> Linear.

Definition Ptr_44 :=
  ((fun A_45 => (FTensor_16 Loc_42 fun l_46 => ((PtsTo_43) l_46) A_45)) :
    (A_45 : Type) -> Linear).

Axiom New_47 : (A_49 : Type) -> A_49 -> (Ptr_44) A_49.

Axiom Free_50 : (A_52 : Type) -> (Ptr_44) A_52 -> Unit_2.

Axiom Get_53 :
  (A_55 : Type) ->
    (l_57 : Loc_42) ->
      ((PtsTo_43) l_57) A_55 ->
        (FTensor_16 A_55 fun __0 => ((PtsTo_43) l_57) A_55).

Axiom Set_58 :
  (A_60 : Type) ->
    (B_62 : Type) ->
      B_62 ->
        (l_64 : Loc_42) -> ((PtsTo_43) l_64) A_60 -> ((PtsTo_43) l_64) B_62.

Inductive le_23 (n_65 : Nat_6) : (Nat_6) -> Type :=
| le_n_24 (n_65 : Nat_6) : (le_23 n_65 n_65)
| le_S_25 (n_65 : Nat_6)
            : (m_69 : Nat_6) ->
                ((le_23 n_65 m_69)) -> (le_23 n_65 (S_8 m_69)).

Definition lt_71 :=
  ((fun m_72 n_73 => (le_23 (S_8 m_72) n_73)) :
    (m_72 : Nat_6) -> (n_73 : Nat_6) -> Type).

Inductive ArrVec_26 (A_75 : Type) (l_76 : Loc_42) : (Nat_6) -> Linear :=
| Nil_27 (A_75 : Type) (l_76 : Loc_42) : (ArrVec_26 A_75 l_76 O_7)
| Cons_28 (A_75 : Type)
            (l_76 : Loc_42)
              : (n_80 : Nat_6) ->
                  (((PtsTo_43) ((add_29) l_76) n_80) A_75) ->
                    ((ArrVec_26 A_75 l_76 n_80)) ->
                      (ArrVec_26 A_75 l_76 (S_8 n_80)).

Definition Array_82 :=
  ((fun A_83 n_84 =>
      (FTensor_16 Loc_42 fun l_85 => (ArrVec_26 A_83 l_85 n_84))) :
    (A_83 : Type) -> (n_84 : Nat_6) -> Linear).

Definition nth_86 :=
  ((fix nth_86 A_87 l_88 m_89 n_90 pf_91 v_92 =>
      (match pf_91 in (le_23 __0 n_90) return
         (ArrVec_26 A_87 l_88 n_90) ->
           (Tensor_14
             ((PtsTo_43) ((add_29) l_88) m_89) A_87
               ((PtsTo_43) ((add_29) l_88) m_89) A_87 >>
                 (ArrVec_26 A_87 l_88 n_90))
       with
       | (le_n_24 ) =>
         fun v_92 =>
           (match v_92 in (ArrVec_26 __0 __0 n_90) return
              match n_90 with
              | (O_7 ) => Base_4
              | (S_8 n0_93) =>
                (Eq_0 Nat_6 m_89 n0_93) >>
                  (Tensor_14
                    ((PtsTo_43) ((add_29) l_88) n0_93) A_87
                      ((PtsTo_43) ((add_29) l_88) n0_93) A_87 >>
                        (ArrVec_26 A_87 l_88 n_90))
              end
            with
            | (Nil_27 ) => ll_5
            | (Cons_28 n_90 c_94 v_92) =>
              fun __0 => (tpair_15 c_94 fun c_94 => (Cons_28 n_90 c_94 v_92))
            end) refl_1
       | (le_S_25 __0 pf_91) =>
         fun v_92 =>
           (match v_92 in (ArrVec_26 __0 __0 n_90) return
              match n_90 with
              | (O_7 ) => Base_4
              | (S_8 n0_95) =>
                ((lt_71) m_89) n0_95 >>
                  (Tensor_14
                    ((PtsTo_43) ((add_29) l_88) m_89) A_87
                      ((PtsTo_43) ((add_29) l_88) m_89) A_87 >>
                        (ArrVec_26 A_87 l_88 n_90))
              end
            with
            | (Nil_27 ) => ll_5
            | (Cons_28 n_90 c0_96 v0_97) =>
              fun pf_91 =>
                let (tpair_15 c_98 f_99) :=
                  ((((((nth_86) A_87) l_88) m_89) n_90) pf_91) v0_97
                in
                (tpair_15 c_98 fun c_98 => (Cons_28 n_90 c0_96 (f_99) c_98))
            end) pf_91
       end) v_92) :
    (A_87 : Type) ->
      (l_88 : Nat_6) ->
        (m_89 : Nat_6) ->
          (n_90 : Nat_6) ->
            (pf_91 : ((lt_71) m_89) n_90) ->
              (v_92 : (ArrVec_26 A_87 l_88 n_90)) ->
                (Tensor_14
                  ((PtsTo_43) ((add_29) l_88) m_89) A_87
                    ((PtsTo_43) ((add_29) l_88) m_89) A_87 >>
                      (ArrVec_26 A_87 l_88 n_90))).

Definition index_100 :=
  ((fun A_101 m_102 n_103 pf_104 a_105 =>
      let (fpair_17 l_107 v_108) := a_105 in
      let (tpair_15 c_109 f_110) :=
        ((((((nth_86) A_101) l_107) m_102) n_103) pf_104) v_108
      in
      let (fpair_17 x_112 c_109) :=
        (((Get_53) A_101) ((add_29) l_107) m_102) c_109
      in (fpair_17 x_112 (fpair_17 l_107 (f_110) c_109))) :
    (A_101 : Type) ->
      (m_102 : Nat_6) ->
        (n_103 : Nat_6) ->
          (pf_104 : ((lt_71) m_102) n_103) ->
            (a_105 : ((Array_82) A_101) n_103) ->
              (FTensor_16 A_101 fun __0 => ((Array_82) A_101) n_103)).

Definition main_113 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_227 : Type) (x_228 : A_227) : (A_227) -> Type :=
| refl_1 (A_230 : Type) (x_231 : A_230) : (Eq_0 A_230 x_231 x_231).

Definition Eq_trans_232 :=
  ((fun A_233 x_234 y_235 z_236 e1_237 e2_238 =>
      match e2_238 in (Eq_0 __240 __241 y_242) return
        (Eq_0 A_233 x_234 y_242)
      with
      | (refl_1 ) => e1_237
      end) :
    (A_243 : Type) ->
      (x_244 : A_243) ->
        (y_245 : A_243) ->
          (z_246 : A_243) ->
            (e1_247 : (Eq_0 A_243 x_244 y_245)) ->
              (e2_248 : (Eq_0 A_243 y_245 z_246)) -> (Eq_0 A_243 x_244 z_246)).

Definition Eq_sym_249 :=
  ((fun A_250 x_251 y_252 e_253 =>
      match e_253 in (Eq_0 __255 __256 y_257) return (Eq_0 A_250 y_257 x_251)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_258 : Type) ->
      (x_259 : A_258) ->
        (y_260 : A_258) ->
          (e_261 : (Eq_0 A_258 x_259 y_260)) -> (Eq_0 A_258 y_260 x_259)).

Definition TyInd_262 :=
  ((fun A_263 x_264 y_265 P_266 e_267 f_268 =>
      match e_267 in (Eq_0 __270 __271 y_272) return (P_266) y_272 with
      | (refl_1 ) => f_268
      end) :
    (A_273 : Type) ->
      (x_274 : A_273) ->
        (y_275 : A_273) ->
          (P_276 : A_273 -> Type) ->
            (e_278 : (Eq_0 A_273 x_274 y_275)) ->
              (f_279 : (P_276) x_274) -> (P_276) y_275).

Definition LnInd_280 :=
  ((fun A_281 x_282 y_283 P_284 e_285 f_286 =>
      match e_285 in (Eq_0 __288 __289 y_290) return (P_284) y_290 with
      | (refl_1 ) => f_286
      end) :
    (A_291 : Type) ->
      (x_292 : A_291) ->
        (y_293 : A_291) ->
          (P_294 : A_291 -> Linear) ->
            (e_296 : (Eq_0 A_291 x_292 y_293)) ->
              (f_297 : (P_294) x_292) -> (P_294) y_293).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_299 :=
  ((fix add_300 m_301 n_302 =>
      match m_301 with
      | (O_7 ) => n_302
      | (S_8 m_303) => (S_8 ((add_300) m_303) n_302)
      end) :
    (m_304 : Nat_6) -> (n_305 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_306 : Type) (F_307 : A_306 -> Type) : Type :=
| pair_13 (A_309 : Type)
            (F_310 : A_309 -> Type)
              : (x_312 : A_309) -> ((F_310) x_312) -> (Sigma_12 A_309 F_310).

Inductive Tensor_14 (A_314 : Linear) (B_315 : Linear) : Linear :=
| tpair_15 (A_316 : Linear)
             (B_317 : Linear) : (A_316) -> (B_317) -> (Tensor_14 A_316 B_317).

Inductive FTensor_16 (A_320 : Type) (F_321 : A_320 -> Linear) : Linear :=
| fpair_17 (A_323 : Type)
             (F_324 : A_323 -> Linear)
               : (x_326 : A_323) ->
                   ((F_324) x_326) -> (FTensor_16 A_323 F_324).

Definition Loc_328 := ((Nat_6) : Type).

Axiom PtsTo_329 : Loc_328 -> Type -> Linear.

Definition Ptr_332 :=
  ((fun A_333 => (FTensor_16 Loc_328 fun l_334 => ((PtsTo_329) l_334) A_333)) :
    (A_335 : Type) -> Linear).

Axiom New_336 : (A_337 : Type) -> A_337 -> (Ptr_332) A_337.

Axiom Free_339 : (A_340 : Type) -> (Ptr_332) A_340 -> Unit_2.

Axiom Get_342 :
  (A_343 : Type) ->
    (l_344 : Loc_328) ->
      ((PtsTo_329) l_344) A_343 ->
        (FTensor_16 A_343 fun __346 => ((PtsTo_329) l_344) A_343).

Axiom Set_347 :
  (A_348 : Type) ->
    (B_349 : Type) ->
      B_349 ->
        (l_351 : Loc_328) ->
          ((PtsTo_329) l_351) A_348 -> ((PtsTo_329) l_351) B_349.

Inductive le_23 (n_353 : Nat_6) : (Nat_6) -> Type :=
| le_n_24 (n_355 : Nat_6) : (le_23 n_355 n_355)
| le_S_25 (n_356 : Nat_6)
            : (m_357 : Nat_6) ->
                ((le_23 n_356 m_357)) -> (le_23 n_356 (S_8 m_357)).

Definition lt_359 :=
  ((fun m_360 n_361 => (le_23 (S_8 m_360) n_361)) :
    (m_362 : Nat_6) -> (n_363 : Nat_6) -> Type).

Inductive ArrVec_26 (A_364 : Type) (l_365 : Loc_328) : (Nat_6) -> Linear :=
| Nil_27 (A_367 : Type) (l_368 : Loc_328) : (ArrVec_26 A_367 l_368 O_7)
| Cons_28 (A_369 : Type)
            (l_370 : Loc_328)
              : (n_371 : Nat_6) ->
                  (((PtsTo_329) ((add_299) l_370) n_371) A_369) ->
                    ((ArrVec_26 A_369 l_370 n_371)) ->
                      (ArrVec_26 A_369 l_370 (S_8 n_371)).

Definition Array_374 :=
  ((fun A_375 n_376 =>
      (FTensor_16 Loc_328 fun l_377 => (ArrVec_26 A_375 l_377 n_376))) :
    (A_378 : Type) -> (n_379 : Nat_6) -> Linear).

Definition nth_380 :=
  ((fix nth_381 A_382 l_383 m_384 n_385 pf_386 v_387 =>
      (match pf_386 in (le_23 __389 n_390) return
         (ArrVec_26 A_382 l_383 n_390) ->
           (Tensor_14
             ((PtsTo_329) ((add_299) l_383) m_384) A_382
               ((PtsTo_329) ((add_299) l_383) m_384) A_382 >>
                 (ArrVec_26 A_382 l_383 n_390))
       with
       | (le_n_24 ) =>
         fun v_393 =>
           (match v_393 in (ArrVec_26 __395 __396 n_397) return
              match n_397 with
              | (O_7 ) => Base_4
              | (S_8 n0_398) =>
                (Eq_0 Nat_6 m_384 n0_398) >>
                  (Tensor_14
                    ((PtsTo_329) ((add_299) l_383) n0_398) A_382
                      ((PtsTo_329) ((add_299) l_383) n0_398) A_382 >>
                        (ArrVec_26 A_382 l_383 n_397))
              end
            with
            | (Nil_27 ) => ll_5
            | (Cons_28 n_401 c_402 v_403) =>
              fun __404 =>
                (tpair_15 c_402 fun c_405 => (Cons_28 n_401 c_405 v_403))
            end) refl_1
       | (le_S_25 __406 pf_407) =>
         fun v_408 =>
           (match v_408 in (ArrVec_26 __410 __411 n_412) return
              match n_412 with
              | (O_7 ) => Base_4
              | (S_8 n0_413) =>
                ((lt_359) m_384) n0_413 >>
                  (Tensor_14
                    ((PtsTo_329) ((add_299) l_383) m_384) A_382
                      ((PtsTo_329) ((add_299) l_383) m_384) A_382 >>
                        (ArrVec_26 A_382 l_383 n_412))
              end
            with
            | (Nil_27 ) => ll_5
            | (Cons_28 n_416 c0_417 v0_418) =>
              fun pf_419 =>
                let x_420 :=
                  ((((((nth_381) A_382) l_383) m_384) n_416) pf_419) v0_418
                in
                match x_420 with
                | (tpair_15 c_421 f_422) =>
                  (tpair_15 c_421
                              fun c_423 =>
                                (Cons_28 n_416 c0_417 (f_422) c_423))
                end
            end) pf_407
       end) v_387) :
    (A_424 : Type) ->
      (l_425 : Nat_6) ->
        (m_426 : Nat_6) ->
          (n_427 : Nat_6) ->
            (pf_428 : ((lt_359) m_426) n_427) ->
              (v_429 : (ArrVec_26 A_424 l_425 n_427)) ->
                (Tensor_14
                  ((PtsTo_329) ((add_299) l_425) m_426) A_424
                    ((PtsTo_329) ((add_299) l_425) m_426) A_424 >>
                      (ArrVec_26 A_424 l_425 n_427))).

Definition index_431 :=
  ((fun A_432 m_433 n_434 pf_435 a_436 =>
      let x_437 := a_436 in
      match x_437 with
      | (fpair_17 l_438 v_439) =>
        let x_440 := ((((((nth_380) A_432) l_438) m_433) n_434) pf_435) v_439
        in
        match x_440 with
        | (tpair_15 c_441 f_442) =>
          let x_443 := (((Get_342) A_432) ((add_299) l_438) m_433) c_441 in
          match x_443 with
          | (fpair_17 x_444 c_445) =>
            (fpair_17 x_444 (fpair_17 l_438 (f_442) c_445))
          end
        end
      end) :
    (A_446 : Type) ->
      (m_447 : Nat_6) ->
        (n_448 : Nat_6) ->
          (pf_449 : ((lt_359) m_447) n_448) ->
            (a_450 : ((Array_374) A_446) n_448) ->
              (FTensor_16 A_446 fun __451 => ((Array_374) A_446) n_448)).

Definition main_452 := ((tt_3) : Unit_2).



v_ctx  := {
  main :0 (Unit_2)::w
  index :0
    ((A_30699 : Type) ->
       (m_30700 : Nat_6) ->
         (n_30701 : Nat_6) ->
           (pf_30702 :
             ((((fun m_30703 n_30704 => (le_23 (S_8 m_30703) n_30704)) :
                 (m_30705 : Nat_6) -> (n_30706 : Nat_6) -> Type))
                m_30700)
               n_30701) ->
             (a_30707 :
               ((((fun A_30708 n_30709 =>
                     (FTensor_16
                       ((Nat_6) : Type)
                         fun l_30710 => (ArrVec_26 A_30708 l_30710 n_30709))) :
                   (A_30711 : Type) -> (n_30712 : Nat_6) -> Linear))
                  A_30699)
                 n_30701) ->
               (FTensor_16
                 A_30699
                   fun __30713 =>
                     ((((fun A_30714 n_30715 =>
                           (FTensor_16
                             ((Nat_6) : Type)
                               fun l_30716 =>
                                 (ArrVec_26 A_30714 l_30716 n_30715))) :
                         (A_30717 : Type) -> (n_30718 : Nat_6) -> Linear))
                        A_30699)
                       n_30701))::w
  nth :0
    ((A_30719 : Type) ->
       (l_30720 : Nat_6) ->
         (m_30721 : Nat_6) ->
           (n_30722 : Nat_6) ->
             (pf_30723 :
               ((((fun m_30724 n_30725 => (le_23 (S_8 m_30724) n_30725)) :
                   (m_30726 : Nat_6) -> (n_30727 : Nat_6) -> Type))
                  m_30721)
                 n_30722) ->
               (v_30728 : (ArrVec_26 A_30719 l_30720 n_30722)) ->
                 (Tensor_14
                   ((PtsTo_18)
                      ((((fix add_30729 m_30730 n_30731 =>
                            match m_30730 with
                            | (O_7 ) => n_30731
                            | (S_8 m_30732) =>
                              (S_8 ((add_30729) m_30732) n_30731)
                            end) :
                          (m_30733 : Nat_6) -> (n_30734 : Nat_6) -> Nat_6))
                         l_30720)
                        m_30721)
                     A_30719
                     ((PtsTo_18)
                        ((((fix add_30736 m_30737 n_30738 =>
                              match m_30737 with
                              | (O_7 ) => n_30738
                              | (S_8 m_30739) =>
                                (S_8 ((add_30736) m_30739) n_30738)
                              end) :
                            (m_30740 : Nat_6) -> (n_30741 : Nat_6) -> Nat_6))
                           l_30720)
                          m_30721)
                       A_30719 >> (ArrVec_26 A_30719 l_30720 n_30722)))::w
  Array :0 ((A_30742 : Type) -> (n_30743 : Nat_6) -> Linear)::w
  lt :0 ((m_30744 : Nat_6) -> (n_30745 : Nat_6) -> Type)::w
  Set :0
    ((A_30746 : Type) ->
       (B_30747 : Type) ->
         B_30747 ->
           (l_30749 : ((Nat_6) : Type)) ->
             ((PtsTo_18) l_30749) A_30746 -> ((PtsTo_18) l_30749) B_30747)::w
  Get :0
    ((A_30751 : Type) ->
       (l_30752 : ((Nat_6) : Type)) ->
         ((PtsTo_18) l_30752) A_30751 ->
           (FTensor_16 A_30751 fun __30754 => ((PtsTo_18) l_30752) A_30751))::w
  Free :0
    ((A_30755 : Type) ->
       (((fun A_30757 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_30758 => ((PtsTo_18) l_30758) A_30757)) :
          (A_30759 : Type) -> Linear))
         A_30755 -> Unit_2)::w
  New :0
    ((A_30760 : Type) ->
       A_30760 ->
         (((fun A_30762 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_30763 => ((PtsTo_18) l_30763) A_30762)) :
            (A_30764 : Type) -> Linear))
           A_30760)::w
  Ptr :0 ((A_30765 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  add :0 ((m_30768 : Nat_6) -> (n_30769 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_30770 : Type) ->
       (x_30771 : A_30770) ->
         (y_30772 : A_30770) ->
           (P_30773 : A_30770 -> Linear) ->
             (e_30775 : (Eq_0 A_30770 x_30771 y_30772)) ->
               (f_30776 : (P_30773) x_30771) -> (P_30773) y_30772)::w
  TyInd :0
    ((A_30777 : Type) ->
       (x_30778 : A_30777) ->
         (y_30779 : A_30777) ->
           (P_30780 : A_30777 -> Type) ->
             (e_30782 : (Eq_0 A_30777 x_30778 y_30779)) ->
               (f_30783 : (P_30780) x_30778) -> (P_30780) y_30779)::w
  Eq_sym :0
    ((A_30784 : Type) ->
       (x_30785 : A_30784) ->
         (y_30786 : A_30784) ->
           (e_30787 : (Eq_0 A_30784 x_30785 y_30786)) ->
             (Eq_0 A_30784 y_30786 x_30785))::w
  Eq_trans :0
    ((A_30788 : Type) ->
       (x_30789 : A_30788) ->
         (y_30790 : A_30788) ->
           (z_30791 : A_30788) ->
             (e1_30792 : (Eq_0 A_30788 x_30789 y_30790)) ->
               (e2_30793 : (Eq_0 A_30788 y_30790 z_30791)) ->
                 (Eq_0 A_30788 x_30789 z_30791))::w
}

tt_3

