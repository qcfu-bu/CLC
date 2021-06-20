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
        ((((((nth_92) A_107) l_113) m_108) n_109) pf_110) v_114
      in
      let (fpair_17 x_118 c_115) :=
        (((Get_59) A_107) ((add_29) l_113) m_108) c_115
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
          (P_306 : A_303 -> Type) ->
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
          (P_324 : A_321 -> Linear) ->
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

Inductive Sigma_12 (A_336 : Type) (F_337 : A_336 -> Type) : Type :=
| pair_13 (A_339 : Type)
            (F_340 : A_339 -> Type)
              : (x_342 : A_339) -> ((F_340) x_342) -> (Sigma_12 A_339 F_340).

Inductive Tensor_14 (A_344 : Linear) (B_345 : Linear) : Linear :=
| tpair_15 (A_346 : Linear)
             (B_347 : Linear) : (A_346) -> (B_347) -> (Tensor_14 A_346 B_347).

Inductive FTensor_16 (A_350 : Type) (F_351 : A_350 -> Linear) : Linear :=
| fpair_17 (A_353 : Type)
             (F_354 : A_353 -> Linear)
               : (x_356 : A_353) ->
                   ((F_354) x_356) -> (FTensor_16 A_353 F_354).

Axiom unsafeC_358 : (A_359 : Linear) -> A_359 -> Unit_2.

Axiom unsafeP_361 : (A_362 : Linear) -> A_362.

Definition Loc_363 := ((Nat_6) : Type).

Axiom PtsTo_364 : Loc_363 -> Type -> Linear.

Definition Ptr_367 :=
  ((fun A_368 => (FTensor_16 Loc_363 fun l_369 => ((PtsTo_364) l_369) A_368)) :
    (A_370 : Type) -> Linear).

Axiom New_371 : (A_372 : Type) -> A_372 -> (Ptr_367) A_372.

Axiom Free_374 : (A_375 : Type) -> (Ptr_367) A_375 -> Unit_2.

Axiom Get_377 :
  (A_378 : Type) ->
    (l_379 : Loc_363) ->
      ((PtsTo_364) l_379) A_378 ->
        (FTensor_16 A_378 fun __381 => ((PtsTo_364) l_379) A_378).

Axiom Set_382 :
  (A_383 : Type) ->
    (B_384 : Type) ->
      B_384 ->
        (l_386 : Loc_363) ->
          ((PtsTo_364) l_386) A_383 -> ((PtsTo_364) l_386) B_384.

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
         (ArrVec_28 A_417 l_418 n_425) ->
           (Tensor_14
             ((PtsTo_364) ((add_329) l_418) m_419) A_417
               ((PtsTo_364) ((add_329) l_418) m_419) A_417 >>
                 (ArrVec_28 A_417 l_418 n_425))
       with
       | (le_n_26 ) =>
         fun v_428 =>
           (match v_428 in (ArrVec_28 __430 __431 n_432) return
              match n_432 with
              | (O_7 ) => Base_4
              | (S_8 n0_433) =>
                (Eq_0 Nat_6 m_419 n0_433) >>
                  (Tensor_14
                    ((PtsTo_364) ((add_329) l_418) n0_433) A_417
                      ((PtsTo_364) ((add_329) l_418) n0_433) A_417 >>
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
                ((lt_394) m_419) n0_448 >>
                  (Tensor_14
                    ((PtsTo_364) ((add_329) l_418) m_419) A_417
                      ((PtsTo_364) ((add_329) l_418) m_419) A_417 >>
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
                    ((PtsTo_364) ((add_329) l_460) m_461) A_459 >>
                      (ArrVec_28 A_459 l_460 n_462))).

Definition index_466 :=
  ((fun A_467 m_468 n_469 pf_470 a_471 =>
      let x_472 := a_471 in
      match x_472 with
      | (fpair_17 l_473 v_474) =>
        let x_475 := ((((((nth_415) A_467) l_473) m_468) n_469) pf_470) v_474
        in
        match x_475 with
        | (tpair_15 c_476 f_477) =>
          let x_478 := (((Get_377) A_467) ((add_329) l_473) m_468) c_476 in
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



v_ctx  := {
  main :0 (Unit_2)::w
  silly :0
    ((m_76897 : Nat_6) ->
       (n_76898 : Nat_6) ->
         (pf_76899 :
           ((((fun m_76900 n_76901 => (le_25 (S_8 m_76900) n_76901)) :
               (m_76902 : Nat_6) -> (n_76903 : Nat_6) -> Type))
              m_76897)
             n_76898) ->
           (a_76904 :
             ((((fun A_76905 n_76906 =>
                   (FTensor_16
                     ((Nat_6) : Type)
                       fun l_76907 => (ArrVec_28 A_76905 l_76907 n_76906))) :
                 (A_76908 : Type) -> (n_76909 : Nat_6) -> Linear))
                (((Sigma_12 Nat_6 fun x_76910 => (Eq_0 Nat_6 x_76910 O_7))) :
                  Type))
               n_76898) ->
             ((((fun A_76911 n_76912 =>
                   (FTensor_16
                     ((Nat_6) : Type)
                       fun l_76913 => (ArrVec_28 A_76911 l_76913 n_76912))) :
                 (A_76914 : Type) -> (n_76915 : Nat_6) -> Linear))
                (((Sigma_12 Nat_6 fun x_76916 => (Eq_0 Nat_6 x_76916 O_7))) :
                  Type))
               n_76898)::w
  Just0 :0 (Type)::w
  index :0
    ((A_76917 : Type) ->
       (m_76918 : Nat_6) ->
         (n_76919 : Nat_6) ->
           (pf_76920 :
             ((((fun m_76921 n_76922 => (le_25 (S_8 m_76921) n_76922)) :
                 (m_76923 : Nat_6) -> (n_76924 : Nat_6) -> Type))
                m_76918)
               n_76919) ->
             (a_76925 :
               ((((fun A_76926 n_76927 =>
                     (FTensor_16
                       ((Nat_6) : Type)
                         fun l_76928 => (ArrVec_28 A_76926 l_76928 n_76927))) :
                   (A_76929 : Type) -> (n_76930 : Nat_6) -> Linear))
                  A_76917)
                 n_76919) ->
               (FTensor_16
                 A_76917
                   fun __76931 =>
                     ((((fun A_76932 n_76933 =>
                           (FTensor_16
                             ((Nat_6) : Type)
                               fun l_76934 =>
                                 (ArrVec_28 A_76932 l_76934 n_76933))) :
                         (A_76935 : Type) -> (n_76936 : Nat_6) -> Linear))
                        A_76917)
                       n_76919))::w
  nth :0
    ((A_76937 : Type) ->
       (l_76938 : Nat_6) ->
         (m_76939 : Nat_6) ->
           (n_76940 : Nat_6) ->
             (pf_76941 :
               ((((fun m_76942 n_76943 => (le_25 (S_8 m_76942) n_76943)) :
                   (m_76944 : Nat_6) -> (n_76945 : Nat_6) -> Type))
                  m_76939)
                 n_76940) ->
               (v_76946 : (ArrVec_28 A_76937 l_76938 n_76940)) ->
                 (Tensor_14
                   ((PtsTo_20)
                      ((((fix add_76947 m_76948 n_76949 =>
                            match m_76948 with
                            | (O_7 ) => n_76949
                            | (S_8 m_76950) =>
                              (S_8 ((add_76947) m_76950) n_76949)
                            end) :
                          (m_76951 : Nat_6) -> (n_76952 : Nat_6) -> Nat_6))
                         l_76938)
                        m_76939)
                     A_76937
                     ((PtsTo_20)
                        ((((fix add_76954 m_76955 n_76956 =>
                              match m_76955 with
                              | (O_7 ) => n_76956
                              | (S_8 m_76957) =>
                                (S_8 ((add_76954) m_76957) n_76956)
                              end) :
                            (m_76958 : Nat_6) -> (n_76959 : Nat_6) -> Nat_6))
                           l_76938)
                          m_76939)
                       A_76937 >> (ArrVec_28 A_76937 l_76938 n_76940)))::w
  Array :0 ((A_76960 : Type) -> (n_76961 : Nat_6) -> Linear)::w
  lt :0 ((m_76962 : Nat_6) -> (n_76963 : Nat_6) -> Type)::w
  Set :0
    ((A_76964 : Type) ->
       (B_76965 : Type) ->
         B_76965 ->
           (l_76967 : ((Nat_6) : Type)) ->
             ((PtsTo_20) l_76967) A_76964 -> ((PtsTo_20) l_76967) B_76965)::w
  Get :0
    ((A_76969 : Type) ->
       (l_76970 : ((Nat_6) : Type)) ->
         ((PtsTo_20) l_76970) A_76969 ->
           (FTensor_16 A_76969 fun __76972 => ((PtsTo_20) l_76970) A_76969))::w
  Free :0
    ((A_76973 : Type) ->
       (((fun A_76975 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_76976 => ((PtsTo_20) l_76976) A_76975)) :
          (A_76977 : Type) -> Linear))
         A_76973 -> Unit_2)::w
  New :0
    ((A_76978 : Type) ->
       A_76978 ->
         (((fun A_76980 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_76981 => ((PtsTo_20) l_76981) A_76980)) :
            (A_76982 : Type) -> Linear))
           A_76978)::w
  Ptr :0 ((A_76983 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  unsafeP :0 ((A_76986 : Linear) -> A_76986)::w
  unsafeC :0 ((A_76987 : Linear) -> A_76987 -> Unit_2)::w
  add :0 ((m_76989 : Nat_6) -> (n_76990 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_76991 : Type) ->
       (x_76992 : A_76991) ->
         (y_76993 : A_76991) ->
           (P_76994 : A_76991 -> Linear) ->
             (e_76996 : (Eq_0 A_76991 x_76992 y_76993)) ->
               (f_76997 : (P_76994) x_76992) -> (P_76994) y_76993)::w
  TyInd :0
    ((A_76998 : Type) ->
       (x_76999 : A_76998) ->
         (y_77000 : A_76998) ->
           (P_77001 : A_76998 -> Type) ->
             (e_77003 : (Eq_0 A_76998 x_76999 y_77000)) ->
               (f_77004 : (P_77001) x_76999) -> (P_77001) y_77000)::w
  Eq_sym :0
    ((A_77005 : Type) ->
       (x_77006 : A_77005) ->
         (y_77007 : A_77005) ->
           (e_77008 : (Eq_0 A_77005 x_77006 y_77007)) ->
             (Eq_0 A_77005 y_77007 x_77006))::w
  Eq_trans :0
    ((A_77009 : Type) ->
       (x_77010 : A_77009) ->
         (y_77011 : A_77009) ->
           (z_77012 : A_77009) ->
             (e1_77013 : (Eq_0 A_77009 x_77010 y_77011)) ->
               (e2_77014 : (Eq_0 A_77009 y_77011 z_77012)) ->
                 (Eq_0 A_77009 x_77010 z_77012))::w
}

tt_3

