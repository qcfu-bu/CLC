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

Inductive le_25 (n_71 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_71 : Nat_6) : (le_25 n_71 n_71)
| le_S_27 (n_71 : Nat_6)
            : (m_75 : Nat_6) ->
                ((le_25 n_71 m_75)) -> (le_25 n_71 (S_8 m_75)).

Definition lt_77 :=
  ((fun m_78 n_79 => (le_25 (S_8 m_78) n_79)) :
    (m_78 : Nat_6) -> (n_79 : Nat_6) -> Type).

Inductive ArrVec_28 (A_81 : Type) (l_82 : Loc_48) : (Nat_6) -> Linear :=
| Nil_29 (A_81 : Type) (l_82 : Loc_48) : (ArrVec_28 A_81 l_82 O_7)
| Cons_30 (A_81 : Type)
            (l_82 : Loc_48)
              : (n_86 : Nat_6) ->
                  (((PtsTo_49) ((add_29) l_82) n_86) A_81) ->
                    ((ArrVec_28 A_81 l_82 n_86)) ->
                      (ArrVec_28 A_81 l_82 (S_8 n_86)).

Definition Array_88 :=
  ((fun A_89 n_90 =>
      (FTensor_16 Loc_48 fun l_91 => (ArrVec_28 A_89 l_91 n_90))) :
    (A_89 : Type) -> (n_90 : Nat_6) -> Linear).

Definition nth_92 :=
  ((fix nth_92 A_93 l_94 m_95 n_96 pf_97 v_98 =>
      (match pf_97 in (le_25 __0 n_96) return
         (ArrVec_28 A_93 l_94 n_96) ->
           (Tensor_14
             ((PtsTo_49) ((add_29) l_94) m_95) A_93
               ((PtsTo_49) ((add_29) l_94) m_95) A_93 >>
                 (ArrVec_28 A_93 l_94 n_96))
       with
       | (le_n_26 ) =>
         fun v_98 =>
           (match v_98 in (ArrVec_28 __0 __0 n_96) return
              match n_96 with
              | (O_7 ) => Base_4
              | (S_8 n0_99) =>
                (Eq_0 Nat_6 m_95 n0_99) >>
                  (Tensor_14
                    ((PtsTo_49) ((add_29) l_94) n0_99) A_93
                      ((PtsTo_49) ((add_29) l_94) n0_99) A_93 >>
                        (ArrVec_28 A_93 l_94 n_96))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_96 c_100 v_98) =>
              fun __0 =>
                (tpair_15 c_100 fun c_100 => (Cons_30 n_96 c_100 v_98))
            end) refl_1
       | (le_S_27 __0 pf_97) =>
         fun v_98 =>
           (match v_98 in (ArrVec_28 __0 __0 n_96) return
              match n_96 with
              | (O_7 ) => Base_4
              | (S_8 n0_101) =>
                ((lt_77) m_95) n0_101 >>
                  (Tensor_14
                    ((PtsTo_49) ((add_29) l_94) m_95) A_93
                      ((PtsTo_49) ((add_29) l_94) m_95) A_93 >>
                        (ArrVec_28 A_93 l_94 n_96))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_96 c0_102 v0_103) =>
              fun pf_97 =>
                let (tpair_15 c_104 f_105) :=
                  ((((((nth_92) A_93) l_94) m_95) n_96) pf_97) v0_103
                in
                (tpair_15 c_104
                            fun c_104 => (Cons_30 n_96 c0_102 (f_105) c_104))
            end) pf_97
       end) v_98) :
    (A_93 : Type) ->
      (l_94 : Nat_6) ->
        (m_95 : Nat_6) ->
          (n_96 : Nat_6) ->
            (pf_97 : ((lt_77) m_95) n_96) ->
              (v_98 : (ArrVec_28 A_93 l_94 n_96)) ->
                (Tensor_14
                  ((PtsTo_49) ((add_29) l_94) m_95) A_93
                    ((PtsTo_49) ((add_29) l_94) m_95) A_93 >>
                      (ArrVec_28 A_93 l_94 n_96))).

Definition index_106 :=
  ((fun A_107 m_108 n_109 pf_110 a_111 =>
      let (fpair_17 l_113 v_114) := a_111 in
      let (tpair_15 c_115 f_116) :=
        ((((((nth_92) ?0) l_113) m_108) n_109) pf_110) v_114
      in
      let (fpair_17 x_118 c_115) :=
        (((Get_59) ?1) ((add_29) l_113) m_108) c_115
      in (fpair_17 x_118 (fpair_17 l_113 (f_116) c_115))) :
    (A_107 : Type) ->
      (m_108 : Nat_6) ->
        (n_109 : Nat_6) ->
          (pf_110 : ((lt_77) m_108) n_109) ->
            (a_111 : ((Array_88) A_107) n_109) ->
              (FTensor_16 A_107 fun __0 => ((Array_88) A_107) n_109)).

Definition Just0_119 :=
  (((Sigma_12 Nat_6 fun x_120 => (Eq_0 Nat_6 x_120 O_7))) : Type).

Definition silly_121 :=
  ((fun m_122 n_123 pf_124 a_125 =>
      let (fpair_17 x_pf_127 a_125) :=
        (((((index_106) Just0_119) m_122) n_123) pf_124) a_125
      in
      let (fpair_17 y_pf_129 a_125) :=
        (((((index_106) Just0_119) m_122) n_123) pf_124) a_125
      in
      let (pair_13 x_130 pf1_131) := x_pf_127 in
      let (pair_13 y_132 pf2_133) := y_pf_129 in
      let pf2_133 := ((((Eq_sym_10) Nat_6) y_132) O_7) pf2_133 in
      let pf_124 :=
        ((((((((Eq_trans_3) Nat_6) x_130) O_7) y_132) pf1_131) pf2_133) :
          (Eq_0 Nat_6 x_130 y_132))
      in a_125) :
    (m_122 : Nat_6) ->
      (n_123 : Nat_6) ->
        (pf_124 : ((lt_77) m_122) n_123) ->
          (a_125 : ((Array_88) Just0_119) n_123) ->
            ((Array_88) Just0_119) n_123).

Definition main_134 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_257 : Type) (x_258 : A_257) : (A_257) -> Type :=
| refl_1 (A_260 : Type) (x_261 : A_260) : (Eq_0 A_260 x_261 x_261).

Definition Eq_trans_262 :=
  ((fun A_263 x_264 y_265 z_266 e1_267 e2_268 =>
      match e2_268 in (Eq_0 __270 __271 y_272) return
        (Eq_0 A_263 x_264 y_272)
      with
      | (refl_1 ) => e1_267
      end) :
    (A_273 : Type) ->
      (x_274 : A_273) ->
        (y_275 : A_273) ->
          (z_276 : A_273) ->
            (e1_277 : (Eq_0 A_273 x_274 y_275)) ->
              (e2_278 : (Eq_0 A_273 y_275 z_276)) -> (Eq_0 A_273 x_274 z_276)).

Definition Eq_sym_279 :=
  ((fun A_280 x_281 y_282 e_283 =>
      match e_283 in (Eq_0 __285 __286 y_287) return (Eq_0 A_280 y_287 x_281)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_288 : Type) ->
      (x_289 : A_288) ->
        (y_290 : A_288) ->
          (e_291 : (Eq_0 A_288 x_289 y_290)) -> (Eq_0 A_288 y_290 x_289)).

Definition TyInd_292 :=
  ((fun A_293 x_294 y_295 P_296 e_297 f_298 =>
      match e_297 in (Eq_0 __300 __301 y_302) return (P_296) y_302 with
      | (refl_1 ) => f_298
      end) :
    (A_303 : Type) ->
      (x_304 : A_303) ->
        (y_305 : A_303) ->
          (P_306 : (A_303) -> Type) ->
            (e_308 : (Eq_0 A_303 x_304 y_305)) ->
              (f_309 : (P_306) x_304) -> (P_306) y_305).

Definition LnInd_310 :=
  ((fun A_311 x_312 y_313 P_314 e_315 f_316 =>
      match e_315 in (Eq_0 __318 __319 y_320) return (P_314) y_320 with
      | (refl_1 ) => f_316
      end) :
    (A_321 : Type) ->
      (x_322 : A_321) ->
        (y_323 : A_321) ->
          (P_324 : (A_321) -> Linear) ->
            (e_326 : (Eq_0 A_321 x_322 y_323)) ->
              (f_327 : (P_324) x_322) -> (P_324) y_323).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_329 :=
  ((fix add_330 m_331 n_332 =>
      match m_331 with
      | (O_7 ) => n_332
      | (S_8 m_333) => (S_8 ((add_330) m_333) n_332)
      end) :
    (m_334 : Nat_6) -> (n_335 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_336 : Type) (F_337 : (A_336) -> Type) : Type :=
| pair_13 (A_339 : Type)
            (F_340 : (A_339) -> Type)
              : (x_342 : A_339) -> ((F_340) x_342) -> (Sigma_12 A_339 F_340).

Inductive Tensor_14 (A_344 : Linear) (B_345 : Linear) : Linear :=
| tpair_15 (A_346 : Linear)
             (B_347 : Linear) : (A_346) -> (B_347) -> (Tensor_14 A_346 B_347).

Inductive FTensor_16 (A_350 : Type) (F_351 : (A_350) -> Linear) : Linear :=
| fpair_17 (A_353 : Type)
             (F_354 : (A_353) -> Linear)
               : (x_356 : A_353) ->
                   ((F_354) x_356) -> (FTensor_16 A_353 F_354).

Axiom unsafeC_358 : (A_359 : Linear) -> (A_359) -> Unit_2.

Axiom unsafeP_361 : (A_362 : Linear) -> A_362.

Definition Loc_363 := ((Nat_6) : Type).

Axiom PtsTo_364 : (Loc_363) -> (Type) -> Linear.

Definition Ptr_367 :=
  ((fun A_368 => (FTensor_16 Loc_363 fun l_369 => ((PtsTo_364) l_369) A_368)) :
    (A_370 : Type) -> Linear).

Axiom New_371 : (A_372 : Type) -> (A_372) -> (Ptr_367) A_372.

Axiom Free_374 : (A_375 : Type) -> ((Ptr_367) A_375) -> Unit_2.

Axiom Get_377 :
  (A_378 : Type) ->
    (l_379 : Loc_363) ->
      (((PtsTo_364) l_379) A_378) ->
        (FTensor_16 A_378 fun __381 => ((PtsTo_364) l_379) A_378).

Axiom Set_382 :
  (A_383 : Type) ->
    (B_384 : Type) ->
      (B_384) ->
        (l_386 : Loc_363) ->
          (((PtsTo_364) l_386) A_383) -> ((PtsTo_364) l_386) B_384.

Inductive le_25 (n_388 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_390 : Nat_6) : (le_25 n_390 n_390)
| le_S_27 (n_391 : Nat_6)
            : (m_392 : Nat_6) ->
                ((le_25 n_391 m_392)) -> (le_25 n_391 (S_8 m_392)).

Definition lt_394 :=
  ((fun m_395 n_396 => (le_25 (S_8 m_395) n_396)) :
    (m_397 : Nat_6) -> (n_398 : Nat_6) -> Type).

Inductive ArrVec_28 (A_399 : Type) (l_400 : Loc_363) : (Nat_6) -> Linear :=
| Nil_29 (A_402 : Type) (l_403 : Loc_363) : (ArrVec_28 A_402 l_403 O_7)
| Cons_30 (A_404 : Type)
            (l_405 : Loc_363)
              : (n_406 : Nat_6) ->
                  (((PtsTo_364) ((add_329) l_405) n_406) A_404) ->
                    ((ArrVec_28 A_404 l_405 n_406)) ->
                      (ArrVec_28 A_404 l_405 (S_8 n_406)).

Definition Array_409 :=
  ((fun A_410 n_411 =>
      (FTensor_16 Loc_363 fun l_412 => (ArrVec_28 A_410 l_412 n_411))) :
    (A_413 : Type) -> (n_414 : Nat_6) -> Linear).

Definition nth_415 :=
  ((fix nth_416 A_417 l_418 m_419 n_420 pf_421 v_422 =>
      (match pf_421 in (le_25 __424 n_425) return
         ((ArrVec_28 A_417 l_418 n_425)) ->
           (Tensor_14
             ((PtsTo_364) ((add_329) l_418) m_419) A_417
               (((PtsTo_364) ((add_329) l_418) m_419) A_417) >>
                 (ArrVec_28 A_417 l_418 n_425))
       with
       | (le_n_26 ) =>
         fun v_428 =>
           (match v_428 in (ArrVec_28 __430 __431 n_432) return
              match n_432 with
              | (O_7 ) => Base_4
              | (S_8 n0_433) =>
                ((Eq_0 Nat_6 m_419 n0_433)) >>
                  (Tensor_14
                    ((PtsTo_364) ((add_329) l_418) n0_433) A_417
                      (((PtsTo_364) ((add_329) l_418) n0_433) A_417) >>
                        (ArrVec_28 A_417 l_418 n_432))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_436 c_437 v_438) =>
              fun __439 =>
                (tpair_15 c_437 fun c_440 => (Cons_30 n_436 c_440 v_438))
            end) refl_1
       | (le_S_27 __441 pf_442) =>
         fun v_443 =>
           (match v_443 in (ArrVec_28 __445 __446 n_447) return
              match n_447 with
              | (O_7 ) => Base_4
              | (S_8 n0_448) =>
                (((lt_394) m_419) n0_448) >>
                  (Tensor_14
                    ((PtsTo_364) ((add_329) l_418) m_419) A_417
                      (((PtsTo_364) ((add_329) l_418) m_419) A_417) >>
                        (ArrVec_28 A_417 l_418 n_447))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_451 c0_452 v0_453) =>
              fun pf_454 =>
                let x_455 :=
                  ((((((nth_416) A_417) l_418) m_419) n_451) pf_454) v0_453
                in
                match x_455 with
                | (tpair_15 c_456 f_457) =>
                  (tpair_15 c_456
                              fun c_458 =>
                                (Cons_30 n_451 c0_452 (f_457) c_458))
                end
            end) pf_442
       end) v_422) :
    (A_459 : Type) ->
      (l_460 : Nat_6) ->
        (m_461 : Nat_6) ->
          (n_462 : Nat_6) ->
            (pf_463 : ((lt_394) m_461) n_462) ->
              (v_464 : (ArrVec_28 A_459 l_460 n_462)) ->
                (Tensor_14
                  ((PtsTo_364) ((add_329) l_460) m_461) A_459
                    (((PtsTo_364) ((add_329) l_460) m_461) A_459) >>
                      (ArrVec_28 A_459 l_460 n_462))).

Definition index_466 :=
  ((fun A_467 m_468 n_469 pf_470 a_471 =>
      let x_472 := a_471 in
      match x_472 with
      | (fpair_17 l_473 v_474) =>
        let x_475 :=
          ((((((nth_415)
                 ((((((((((((((((((((((((?0) Eq_trans_262) Eq_sym_279)
                                        TyInd_292)
                                       LnInd_310)
                                      add_329)
                                     unsafeC_358)
                                    unsafeP_361)
                                   Loc_363)
                                  PtsTo_364)
                                 Ptr_367)
                                New_371)
                               Free_374)
                              Get_377)
                             Set_382)
                            lt_394)
                           Array_409)
                          nth_415)
                         A_467)
                        m_468)
                       n_469)
                      pf_470)
                     a_471)
                    l_473)
                   v_474)
                l_473)
               m_468)
              n_469)
             pf_470)
            v_474
        in
        match x_475 with
        | (tpair_15 c_476 f_477) =>
          let x_478 :=
            (((Get_377)
                ((((((((((((((((((((((((((?1) Eq_trans_262) Eq_sym_279)
                                         TyInd_292)
                                        LnInd_310)
                                       add_329)
                                      unsafeC_358)
                                     unsafeP_361)
                                    Loc_363)
                                   PtsTo_364)
                                  Ptr_367)
                                 New_371)
                                Free_374)
                               Get_377)
                              Set_382)
                             lt_394)
                            Array_409)
                           nth_415)
                          A_467)
                         m_468)
                        n_469)
                       pf_470)
                      a_471)
                     l_473)
                    v_474)
                   c_476)
                  f_477)
               ((add_329) l_473) m_468)
              c_476
          in
          match x_478 with
          | (fpair_17 x_479 c_480) =>
            (fpair_17 x_479 (fpair_17 l_473 (f_477) c_480))
          end
        end
      end) :
    (A_481 : Type) ->
      (m_482 : Nat_6) ->
        (n_483 : Nat_6) ->
          (pf_484 : ((lt_394) m_482) n_483) ->
            (a_485 : ((Array_409) A_481) n_483) ->
              (FTensor_16 A_481 fun __486 => ((Array_409) A_481) n_483)).

Definition Just0_487 :=
  (((Sigma_12 Nat_6 fun x_488 => (Eq_0 Nat_6 x_488 O_7))) : Type).

Definition silly_489 :=
  ((fun m_490 n_491 pf_492 a_493 =>
      let x_494 := (((((index_466) Just0_487) m_490) n_491) pf_492) a_493 in
      match x_494 with
      | (fpair_17 x_pf_495 a_496) =>
        let x_497 := (((((index_466) Just0_487) m_490) n_491) pf_492) a_496
        in
        match x_497 with
        | (fpair_17 y_pf_498 a_499) =>
          let x_500 := x_pf_495 in
          match x_500 with
          | (pair_13 x_501 pf1_502) =>
            let x0_503 := y_pf_498 in
            match x0_503 with
            | (pair_13 y_504 pf2_505) =>
              let pf2_506 := ((((Eq_sym_279) Nat_6) y_504) O_7) pf2_505 in
              let pf_507 :=
                ((((((((Eq_trans_262) Nat_6) x_501) O_7) y_504) pf1_502)
                    pf2_506) :
                  (Eq_0 Nat_6 x_501 y_504))
              in a_499
            end
          end
        end
      end) :
    (m_508 : Nat_6) ->
      (n_509 : Nat_6) ->
        (pf_510 : ((lt_394) m_508) n_509) ->
          (a_511 : ((Array_409) Just0_487) n_509) ->
            ((Array_409) Just0_487) n_509).

Definition main_512 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_46996 : Type) (x_46997 : A_46996) : (A_46996) -> Type :=
| refl_1 (A_46999 : Type)
           (x_47000 : A_46999) : (Eq_0 A_46999 x_47000 x_47000).

Definition Eq_trans_47001 :=
  ((fun A_47002 x_47003 y_47004 z_47005 e1_47006 e2_47007 =>
      match e2_47007 in (Eq_0 __47009 __47010 y_47011) return
        (Eq_0 A_47002 x_47003 y_47011)
      with
      | (refl_1 ) => e1_47006
      end) :
    (A_47012 : Type) ->
      (x_47013 : A_47012) ->
        (y_47014 : A_47012) ->
          (z_47015 : A_47012) ->
            (e1_47016 : (Eq_0 A_47012 x_47013 y_47014)) ->
              (e2_47017 : (Eq_0 A_47012 y_47014 z_47015)) ->
                (Eq_0 A_47012 x_47013 z_47015)).

Definition Eq_sym_47018 :=
  ((fun A_47019 x_47020 y_47021 e_47022 =>
      match e_47022 in (Eq_0 __47024 __47025 y_47026) return
        (Eq_0 A_47019 y_47026 x_47020)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_47027 : Type) ->
      (x_47028 : A_47027) ->
        (y_47029 : A_47027) ->
          (e_47030 : (Eq_0 A_47027 x_47028 y_47029)) ->
            (Eq_0 A_47027 y_47029 x_47028)).

Definition TyInd_47031 :=
  ((fun A_47032 x_47033 y_47034 P_47035 e_47036 f_47037 =>
      match e_47036 in (Eq_0 __47039 __47040 y_47041) return
        (P_47035) y_47041
      with
      | (refl_1 ) => f_47037
      end) :
    (A_47042 : Type) ->
      (x_47043 : A_47042) ->
        (y_47044 : A_47042) ->
          (P_47045 : (A_47042) -> Type) ->
            (e_47047 : (Eq_0 A_47042 x_47043 y_47044)) ->
              (f_47048 : (P_47045) x_47043) -> (P_47045) y_47044).

Definition LnInd_47049 :=
  ((fun A_47050 x_47051 y_47052 P_47053 e_47054 f_47055 =>
      match e_47054 in (Eq_0 __47057 __47058 y_47059) return
        (P_47053) y_47059
      with
      | (refl_1 ) => f_47055
      end) :
    (A_47060 : Type) ->
      (x_47061 : A_47060) ->
        (y_47062 : A_47060) ->
          (P_47063 : (A_47060) -> Linear) ->
            (e_47065 : (Eq_0 A_47060 x_47061 y_47062)) ->
              (f_47066 : (P_47063) x_47061) -> (P_47063) y_47062).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_47068 :=
  ((fix add_47069 m_47070 n_47071 =>
      match m_47070 with
      | (O_7 ) => n_47071
      | (S_8 m_47072) => (S_8 ((add_47069) m_47072) n_47071)
      end) :
    (m_47073 : Nat_6) -> (n_47074 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_47075 : Type) (F_47076 : (A_47075) -> Type) : Type :=
| pair_13 (A_47078 : Type)
            (F_47079 : (A_47078) -> Type)
              : (x_47081 : A_47078) ->
                  ((F_47079) x_47081) -> (Sigma_12 A_47078 F_47079).

Inductive Tensor_14 (A_47083 : Linear) (B_47084 : Linear) : Linear :=
| tpair_15 (A_47085 : Linear)
             (B_47086 : Linear)
               : (A_47085) -> (B_47086) -> (Tensor_14 A_47085 B_47086).

Inductive FTensor_16 (A_47089 : Type)
                       (F_47090 : (A_47089) -> Linear) : Linear :=
| fpair_17 (A_47092 : Type)
             (F_47093 : (A_47092) -> Linear)
               : (x_47095 : A_47092) ->
                   ((F_47093) x_47095) -> (FTensor_16 A_47092 F_47093).

Axiom unsafeC_47097 : (A_47098 : Linear) -> (A_47098) -> Unit_2.

Axiom unsafeP_47100 : (A_47101 : Linear) -> A_47101.

Definition Loc_47102 := ((Nat_6) : Type).

Axiom PtsTo_47103 : (Loc_47102) -> (Type) -> Linear.

Definition Ptr_47106 :=
  ((fun A_47107 =>
      (FTensor_16 Loc_47102 fun l_47108 => ((PtsTo_47103) l_47108) A_47107)) :
    (A_47109 : Type) -> Linear).

Axiom New_47110 : (A_47111 : Type) -> (A_47111) -> (Ptr_47106) A_47111.

Axiom Free_47113 : (A_47114 : Type) -> ((Ptr_47106) A_47114) -> Unit_2.

Axiom Get_47116 :
  (A_47117 : Type) ->
    (l_47118 : Loc_47102) ->
      (((PtsTo_47103) l_47118) A_47117) ->
        (FTensor_16 A_47117 fun __47120 => ((PtsTo_47103) l_47118) A_47117).

Axiom Set_47121 :
  (A_47122 : Type) ->
    (B_47123 : Type) ->
      (B_47123) ->
        (l_47125 : Loc_47102) ->
          (((PtsTo_47103) l_47125) A_47122) ->
            ((PtsTo_47103) l_47125) B_47123.

Inductive le_25 (n_47127 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_47129 : Nat_6) : (le_25 n_47129 n_47129)
| le_S_27 (n_47130 : Nat_6)
            : (m_47131 : Nat_6) ->
                ((le_25 n_47130 m_47131)) -> (le_25 n_47130 (S_8 m_47131)).

Definition lt_47133 :=
  ((fun m_47134 n_47135 => (le_25 (S_8 m_47134) n_47135)) :
    (m_47136 : Nat_6) -> (n_47137 : Nat_6) -> Type).

Inductive ArrVec_28 (A_47138 : Type)
                      (l_47139 : Loc_47102) : (Nat_6) -> Linear :=
| Nil_29 (A_47141 : Type)
           (l_47142 : Loc_47102) : (ArrVec_28 A_47141 l_47142 O_7)
| Cons_30 (A_47143 : Type)
            (l_47144 : Loc_47102)
              : (n_47145 : Nat_6) ->
                  (((PtsTo_47103) ((add_47068) l_47144) n_47145) A_47143) ->
                    ((ArrVec_28 A_47143 l_47144 n_47145)) ->
                      (ArrVec_28 A_47143 l_47144 (S_8 n_47145)).

Definition Array_47148 :=
  ((fun A_47149 n_47150 =>
      (FTensor_16
        Loc_47102 fun l_47151 => (ArrVec_28 A_47149 l_47151 n_47150))) :
    (A_47152 : Type) -> (n_47153 : Nat_6) -> Linear).

Definition nth_47154 :=
  ((fix nth_47155 A_47156 l_47157 m_47158 n_47159 pf_47160 v_47161 =>
      (match pf_47160 in (le_25 __47163 n_47164) return
         ((ArrVec_28 A_47156 l_47157 n_47164)) ->
           (Tensor_14
             ((PtsTo_47103) ((add_47068) l_47157) m_47158) A_47156
               (((PtsTo_47103) ((add_47068) l_47157) m_47158) A_47156) >>
                 (ArrVec_28 A_47156 l_47157 n_47164))
       with
       | (le_n_26 ) =>
         fun v_47167 =>
           (match v_47167 in (ArrVec_28 __47169 __47170 n_47171) return
              match n_47171 with
              | (O_7 ) => Base_4
              | (S_8 n0_47172) =>
                ((Eq_0 Nat_6 m_47158 n0_47172)) >>
                  (Tensor_14
                    ((PtsTo_47103) ((add_47068) l_47157) n0_47172) A_47156
                      (((PtsTo_47103) ((add_47068) l_47157) n0_47172) A_47156) >>
                        (ArrVec_28 A_47156 l_47157 n_47171))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_47175 c_47176 v_47177) =>
              fun __47178 =>
                (tpair_15 c_47176
                            fun c_47179 => (Cons_30 n_47175 c_47179 v_47177))
            end) refl_1
       | (le_S_27 __47180 pf_47181) =>
         fun v_47182 =>
           (match v_47182 in (ArrVec_28 __47184 __47185 n_47186) return
              match n_47186 with
              | (O_7 ) => Base_4
              | (S_8 n0_47187) =>
                (((lt_47133) m_47158) n0_47187) >>
                  (Tensor_14
                    ((PtsTo_47103) ((add_47068) l_47157) m_47158) A_47156
                      (((PtsTo_47103) ((add_47068) l_47157) m_47158) A_47156) >>
                        (ArrVec_28 A_47156 l_47157 n_47186))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_47190 c0_47191 v0_47192) =>
              fun pf_47193 =>
                let x_47194 :=
                  ((((((nth_47155) A_47156) l_47157) m_47158) n_47190)
                     pf_47193)
                    v0_47192
                in
                match x_47194 with
                | (tpair_15 c_47195 f_47196) =>
                  (tpair_15 c_47195
                              fun c_47197 =>
                                (Cons_30 n_47190 c0_47191 (f_47196) c_47197))
                end
            end) pf_47181
       end) v_47161) :
    (A_47198 : Type) ->
      (l_47199 : Nat_6) ->
        (m_47200 : Nat_6) ->
          (n_47201 : Nat_6) ->
            (pf_47202 : ((lt_47133) m_47200) n_47201) ->
              (v_47203 : (ArrVec_28 A_47198 l_47199 n_47201)) ->
                (Tensor_14
                  ((PtsTo_47103) ((add_47068) l_47199) m_47200) A_47198
                    (((PtsTo_47103) ((add_47068) l_47199) m_47200) A_47198) >>
                      (ArrVec_28 A_47198 l_47199 n_47201))).

Definition index_47205 :=
  ((fun A_47206 m_47207 n_47208 pf_47209 a_47210 =>
      let x_47211 := a_47210 in
      match x_47211 with
      | (fpair_17 l_47212 v_47213) =>
        let x_47214 :=
          ((((((nth_47154) A_47206) l_47212) m_47207) n_47208) pf_47209)
            v_47213
        in
        match x_47214 with
        | (tpair_15 c_47215 f_47216) =>
          let x_47217 :=
            (((Get_47116) A_47206) ((add_47068) l_47212) m_47207) c_47215
          in
          match x_47217 with
          | (fpair_17 x_47218 c_47219) =>
            (fpair_17 x_47218 (fpair_17 l_47212 (f_47216) c_47219))
          end
        end
      end) :
    (A_47220 : Type) ->
      (m_47221 : Nat_6) ->
        (n_47222 : Nat_6) ->
          (pf_47223 : ((lt_47133) m_47221) n_47222) ->
            (a_47224 : ((Array_47148) A_47220) n_47222) ->
              (FTensor_16
                A_47220 fun __47225 => ((Array_47148) A_47220) n_47222)).

Definition Just0_47226 :=
  (((Sigma_12 Nat_6 fun x_47227 => (Eq_0 Nat_6 x_47227 O_7))) : Type).

Definition silly_47228 :=
  ((fun m_47229 n_47230 pf_47231 a_47232 =>
      let x_47233 :=
        (((((index_47205) Just0_47226) m_47229) n_47230) pf_47231) a_47232
      in
      match x_47233 with
      | (fpair_17 x_pf_47234 a_47235) =>
        let x_47236 :=
          (((((index_47205) Just0_47226) m_47229) n_47230) pf_47231) a_47235
        in
        match x_47236 with
        | (fpair_17 y_pf_47237 a_47238) =>
          let x_47239 := x_pf_47234 in
          match x_47239 with
          | (pair_13 x_47240 pf1_47241) =>
            let x0_47242 := y_pf_47237 in
            match x0_47242 with
            | (pair_13 y_47243 pf2_47244) =>
              let pf2_47245 :=
                ((((Eq_sym_47018) Nat_6) y_47243) O_7) pf2_47244
              in
              let pf_47246 :=
                ((((((((Eq_trans_47001) Nat_6) x_47240) O_7) y_47243)
                     pf1_47241)
                    pf2_47245) :
                  (Eq_0 Nat_6 x_47240 y_47243))
              in a_47238
            end
          end
        end
      end) :
    (m_47247 : Nat_6) ->
      (n_47248 : Nat_6) ->
        (pf_47249 : ((lt_47133) m_47247) n_47248) ->
          (a_47250 : ((Array_47148) Just0_47226) n_47248) ->
            ((Array_47148) Just0_47226) n_47248).

Definition main_47251 := ((tt_3) : Unit_2).



tt_3

