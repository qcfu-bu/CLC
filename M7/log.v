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

Definition Just0_113 :=
  (((Sigma_12 Nat_6 fun x_114 => (Eq_0 Nat_6 x_114 O_7))) : Type).

Definition silly_115 :=
  ((fun m_116 n_117 pf_118 a_119 =>
      let (fpair_17 x_pf_121 a_119) :=
        (((((index_100) Just0_113) m_116) n_117) pf_118) a_119
      in
      let (fpair_17 y_pf_123 a_119) :=
        (((((index_100) Just0_113) m_116) n_117) pf_118) a_119
      in
      let (pair_13 x_124 pf1_125) := x_pf_121 in
      let (pair_13 y_126 pf2_127) := y_pf_123 in
      let pf2_127 := ((((Eq_sym_10) Nat_6) y_126) O_7) pf2_127 in
      let pf_118 :=
        ((((((((Eq_trans_3) Nat_6) x_124) O_7) y_126) pf1_125) pf2_127) :
          (Eq_0 Nat_6 x_124 y_126))
      in a_119) :
    (m_116 : Nat_6) ->
      (n_117 : Nat_6) ->
        (pf_118 : ((lt_71) m_116) n_117) ->
          (a_119 : ((Array_82) Just0_113) n_117) ->
            ((Array_82) Just0_113) n_117).

Definition main_128 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_252 : Type) (x_253 : A_252) : (A_252) -> Type :=
| refl_1 (A_255 : Type) (x_256 : A_255) : (Eq_0 A_255 x_256 x_256).

Definition Eq_trans_257 :=
  ((fun A_258 x_259 y_260 z_261 e1_262 e2_263 =>
      match e2_263 in (Eq_0 __265 __266 y_267) return
        (Eq_0 A_258 x_259 y_267)
      with
      | (refl_1 ) => e1_262
      end) :
    (A_268 : Type) ->
      (x_269 : A_268) ->
        (y_270 : A_268) ->
          (z_271 : A_268) ->
            (e1_272 : (Eq_0 A_268 x_269 y_270)) ->
              (e2_273 : (Eq_0 A_268 y_270 z_271)) -> (Eq_0 A_268 x_269 z_271)).

Definition Eq_sym_274 :=
  ((fun A_275 x_276 y_277 e_278 =>
      match e_278 in (Eq_0 __280 __281 y_282) return (Eq_0 A_275 y_282 x_276)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_283 : Type) ->
      (x_284 : A_283) ->
        (y_285 : A_283) ->
          (e_286 : (Eq_0 A_283 x_284 y_285)) -> (Eq_0 A_283 y_285 x_284)).

Definition TyInd_287 :=
  ((fun A_288 x_289 y_290 P_291 e_292 f_293 =>
      match e_292 in (Eq_0 __295 __296 y_297) return (P_291) y_297 with
      | (refl_1 ) => f_293
      end) :
    (A_298 : Type) ->
      (x_299 : A_298) ->
        (y_300 : A_298) ->
          (P_301 : A_298 -> Type) ->
            (e_303 : (Eq_0 A_298 x_299 y_300)) ->
              (f_304 : (P_301) x_299) -> (P_301) y_300).

Definition LnInd_305 :=
  ((fun A_306 x_307 y_308 P_309 e_310 f_311 =>
      match e_310 in (Eq_0 __313 __314 y_315) return (P_309) y_315 with
      | (refl_1 ) => f_311
      end) :
    (A_316 : Type) ->
      (x_317 : A_316) ->
        (y_318 : A_316) ->
          (P_319 : A_316 -> Linear) ->
            (e_321 : (Eq_0 A_316 x_317 y_318)) ->
              (f_322 : (P_319) x_317) -> (P_319) y_318).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_324 :=
  ((fix add_325 m_326 n_327 =>
      match m_326 with
      | (O_7 ) => n_327
      | (S_8 m_328) => (S_8 ((add_325) m_328) n_327)
      end) :
    (m_329 : Nat_6) -> (n_330 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_331 : Type) (F_332 : A_331 -> Type) : Type :=
| pair_13 (A_334 : Type)
            (F_335 : A_334 -> Type)
              : (x_337 : A_334) -> ((F_335) x_337) -> (Sigma_12 A_334 F_335).

Inductive Tensor_14 (A_339 : Linear) (B_340 : Linear) : Linear :=
| tpair_15 (A_341 : Linear)
             (B_342 : Linear) : (A_341) -> (B_342) -> (Tensor_14 A_341 B_342).

Inductive FTensor_16 (A_345 : Type) (F_346 : A_345 -> Linear) : Linear :=
| fpair_17 (A_348 : Type)
             (F_349 : A_348 -> Linear)
               : (x_351 : A_348) ->
                   ((F_349) x_351) -> (FTensor_16 A_348 F_349).

Definition Loc_353 := ((Nat_6) : Type).

Axiom PtsTo_354 : Loc_353 -> Type -> Linear.

Definition Ptr_357 :=
  ((fun A_358 => (FTensor_16 Loc_353 fun l_359 => ((PtsTo_354) l_359) A_358)) :
    (A_360 : Type) -> Linear).

Axiom New_361 : (A_362 : Type) -> A_362 -> (Ptr_357) A_362.

Axiom Free_364 : (A_365 : Type) -> (Ptr_357) A_365 -> Unit_2.

Axiom Get_367 :
  (A_368 : Type) ->
    (l_369 : Loc_353) ->
      ((PtsTo_354) l_369) A_368 ->
        (FTensor_16 A_368 fun __371 => ((PtsTo_354) l_369) A_368).

Axiom Set_372 :
  (A_373 : Type) ->
    (B_374 : Type) ->
      B_374 ->
        (l_376 : Loc_353) ->
          ((PtsTo_354) l_376) A_373 -> ((PtsTo_354) l_376) B_374.

Inductive le_23 (n_378 : Nat_6) : (Nat_6) -> Type :=
| le_n_24 (n_380 : Nat_6) : (le_23 n_380 n_380)
| le_S_25 (n_381 : Nat_6)
            : (m_382 : Nat_6) ->
                ((le_23 n_381 m_382)) -> (le_23 n_381 (S_8 m_382)).

Definition lt_384 :=
  ((fun m_385 n_386 => (le_23 (S_8 m_385) n_386)) :
    (m_387 : Nat_6) -> (n_388 : Nat_6) -> Type).

Inductive ArrVec_26 (A_389 : Type) (l_390 : Loc_353) : (Nat_6) -> Linear :=
| Nil_27 (A_392 : Type) (l_393 : Loc_353) : (ArrVec_26 A_392 l_393 O_7)
| Cons_28 (A_394 : Type)
            (l_395 : Loc_353)
              : (n_396 : Nat_6) ->
                  (((PtsTo_354) ((add_324) l_395) n_396) A_394) ->
                    ((ArrVec_26 A_394 l_395 n_396)) ->
                      (ArrVec_26 A_394 l_395 (S_8 n_396)).

Definition Array_399 :=
  ((fun A_400 n_401 =>
      (FTensor_16 Loc_353 fun l_402 => (ArrVec_26 A_400 l_402 n_401))) :
    (A_403 : Type) -> (n_404 : Nat_6) -> Linear).

Definition nth_405 :=
  ((fix nth_406 A_407 l_408 m_409 n_410 pf_411 v_412 =>
      (match pf_411 in (le_23 __414 n_415) return
         (ArrVec_26 A_407 l_408 n_415) ->
           (Tensor_14
             ((PtsTo_354) ((add_324) l_408) m_409) A_407
               ((PtsTo_354) ((add_324) l_408) m_409) A_407 >>
                 (ArrVec_26 A_407 l_408 n_415))
       with
       | (le_n_24 ) =>
         fun v_418 =>
           (match v_418 in (ArrVec_26 __420 __421 n_422) return
              match n_422 with
              | (O_7 ) => Base_4
              | (S_8 n0_423) =>
                (Eq_0 Nat_6 m_409 n0_423) >>
                  (Tensor_14
                    ((PtsTo_354) ((add_324) l_408) n0_423) A_407
                      ((PtsTo_354) ((add_324) l_408) n0_423) A_407 >>
                        (ArrVec_26 A_407 l_408 n_422))
              end
            with
            | (Nil_27 ) => ll_5
            | (Cons_28 n_426 c_427 v_428) =>
              fun __429 =>
                (tpair_15 c_427 fun c_430 => (Cons_28 n_426 c_430 v_428))
            end) refl_1
       | (le_S_25 __431 pf_432) =>
         fun v_433 =>
           (match v_433 in (ArrVec_26 __435 __436 n_437) return
              match n_437 with
              | (O_7 ) => Base_4
              | (S_8 n0_438) =>
                ((lt_384) m_409) n0_438 >>
                  (Tensor_14
                    ((PtsTo_354) ((add_324) l_408) m_409) A_407
                      ((PtsTo_354) ((add_324) l_408) m_409) A_407 >>
                        (ArrVec_26 A_407 l_408 n_437))
              end
            with
            | (Nil_27 ) => ll_5
            | (Cons_28 n_441 c0_442 v0_443) =>
              fun pf_444 =>
                let x_445 :=
                  ((((((nth_406) A_407) l_408) m_409) n_441) pf_444) v0_443
                in
                match x_445 with
                | (tpair_15 c_446 f_447) =>
                  (tpair_15 c_446
                              fun c_448 =>
                                (Cons_28 n_441 c0_442 (f_447) c_448))
                end
            end) pf_432
       end) v_412) :
    (A_449 : Type) ->
      (l_450 : Nat_6) ->
        (m_451 : Nat_6) ->
          (n_452 : Nat_6) ->
            (pf_453 : ((lt_384) m_451) n_452) ->
              (v_454 : (ArrVec_26 A_449 l_450 n_452)) ->
                (Tensor_14
                  ((PtsTo_354) ((add_324) l_450) m_451) A_449
                    ((PtsTo_354) ((add_324) l_450) m_451) A_449 >>
                      (ArrVec_26 A_449 l_450 n_452))).

Definition index_456 :=
  ((fun A_457 m_458 n_459 pf_460 a_461 =>
      let x_462 := a_461 in
      match x_462 with
      | (fpair_17 l_463 v_464) =>
        let x_465 := ((((((nth_405) A_457) l_463) m_458) n_459) pf_460) v_464
        in
        match x_465 with
        | (tpair_15 c_466 f_467) =>
          let x_468 := (((Get_367) A_457) ((add_324) l_463) m_458) c_466 in
          match x_468 with
          | (fpair_17 x_469 c_470) =>
            (fpair_17 x_469 (fpair_17 l_463 (f_467) c_470))
          end
        end
      end) :
    (A_471 : Type) ->
      (m_472 : Nat_6) ->
        (n_473 : Nat_6) ->
          (pf_474 : ((lt_384) m_472) n_473) ->
            (a_475 : ((Array_399) A_471) n_473) ->
              (FTensor_16 A_471 fun __476 => ((Array_399) A_471) n_473)).

Definition Just0_477 :=
  (((Sigma_12 Nat_6 fun x_478 => (Eq_0 Nat_6 x_478 O_7))) : Type).

Definition silly_479 :=
  ((fun m_480 n_481 pf_482 a_483 =>
      let x_484 := (((((index_456) Just0_477) m_480) n_481) pf_482) a_483 in
      match x_484 with
      | (fpair_17 x_pf_485 a_486) =>
        let x_487 := (((((index_456) Just0_477) m_480) n_481) pf_482) a_486
        in
        match x_487 with
        | (fpair_17 y_pf_488 a_489) =>
          let x_490 := x_pf_485 in
          match x_490 with
          | (pair_13 x_491 pf1_492) =>
            let x0_493 := y_pf_488 in
            match x0_493 with
            | (pair_13 y_494 pf2_495) =>
              let pf2_496 := ((((Eq_sym_274) Nat_6) y_494) O_7) pf2_495 in
              let pf_497 :=
                ((((((((Eq_trans_257) Nat_6) x_491) O_7) y_494) pf1_492)
                    pf2_496) :
                  (Eq_0 Nat_6 x_491 y_494))
              in a_489
            end
          end
        end
      end) :
    (m_498 : Nat_6) ->
      (n_499 : Nat_6) ->
        (pf_500 : ((lt_384) m_498) n_499) ->
          (a_501 : ((Array_399) Just0_477) n_499) ->
            ((Array_399) Just0_477) n_499).

Definition main_502 := ((tt_3) : Unit_2).



v_ctx  := {
  main :0 (Unit_2)::w
  silly :0
    ((m_75121 : Nat_6) ->
       (n_75122 : Nat_6) ->
         (pf_75123 :
           ((((fun m_75124 n_75125 => (le_23 (S_8 m_75124) n_75125)) :
               (m_75126 : Nat_6) -> (n_75127 : Nat_6) -> Type))
              m_75121)
             n_75122) ->
           (a_75128 :
             ((((fun A_75129 n_75130 =>
                   (FTensor_16
                     ((Nat_6) : Type)
                       fun l_75131 => (ArrVec_26 A_75129 l_75131 n_75130))) :
                 (A_75132 : Type) -> (n_75133 : Nat_6) -> Linear))
                (((Sigma_12 Nat_6 fun x_75134 => (Eq_0 Nat_6 x_75134 O_7))) :
                  Type))
               n_75122) ->
             ((((fun A_75135 n_75136 =>
                   (FTensor_16
                     ((Nat_6) : Type)
                       fun l_75137 => (ArrVec_26 A_75135 l_75137 n_75136))) :
                 (A_75138 : Type) -> (n_75139 : Nat_6) -> Linear))
                (((Sigma_12 Nat_6 fun x_75140 => (Eq_0 Nat_6 x_75140 O_7))) :
                  Type))
               n_75122)::w
  Just0 :0 (Type)::w
  index :0
    ((A_75141 : Type) ->
       (m_75142 : Nat_6) ->
         (n_75143 : Nat_6) ->
           (pf_75144 :
             ((((fun m_75145 n_75146 => (le_23 (S_8 m_75145) n_75146)) :
                 (m_75147 : Nat_6) -> (n_75148 : Nat_6) -> Type))
                m_75142)
               n_75143) ->
             (a_75149 :
               ((((fun A_75150 n_75151 =>
                     (FTensor_16
                       ((Nat_6) : Type)
                         fun l_75152 => (ArrVec_26 A_75150 l_75152 n_75151))) :
                   (A_75153 : Type) -> (n_75154 : Nat_6) -> Linear))
                  A_75141)
                 n_75143) ->
               (FTensor_16
                 A_75141
                   fun __75155 =>
                     ((((fun A_75156 n_75157 =>
                           (FTensor_16
                             ((Nat_6) : Type)
                               fun l_75158 =>
                                 (ArrVec_26 A_75156 l_75158 n_75157))) :
                         (A_75159 : Type) -> (n_75160 : Nat_6) -> Linear))
                        A_75141)
                       n_75143))::w
  nth :0
    ((A_75161 : Type) ->
       (l_75162 : Nat_6) ->
         (m_75163 : Nat_6) ->
           (n_75164 : Nat_6) ->
             (pf_75165 :
               ((((fun m_75166 n_75167 => (le_23 (S_8 m_75166) n_75167)) :
                   (m_75168 : Nat_6) -> (n_75169 : Nat_6) -> Type))
                  m_75163)
                 n_75164) ->
               (v_75170 : (ArrVec_26 A_75161 l_75162 n_75164)) ->
                 (Tensor_14
                   ((PtsTo_18)
                      ((((fix add_75171 m_75172 n_75173 =>
                            match m_75172 with
                            | (O_7 ) => n_75173
                            | (S_8 m_75174) =>
                              (S_8 ((add_75171) m_75174) n_75173)
                            end) :
                          (m_75175 : Nat_6) -> (n_75176 : Nat_6) -> Nat_6))
                         l_75162)
                        m_75163)
                     A_75161
                     ((PtsTo_18)
                        ((((fix add_75178 m_75179 n_75180 =>
                              match m_75179 with
                              | (O_7 ) => n_75180
                              | (S_8 m_75181) =>
                                (S_8 ((add_75178) m_75181) n_75180)
                              end) :
                            (m_75182 : Nat_6) -> (n_75183 : Nat_6) -> Nat_6))
                           l_75162)
                          m_75163)
                       A_75161 >> (ArrVec_26 A_75161 l_75162 n_75164)))::w
  Array :0 ((A_75184 : Type) -> (n_75185 : Nat_6) -> Linear)::w
  lt :0 ((m_75186 : Nat_6) -> (n_75187 : Nat_6) -> Type)::w
  Set :0
    ((A_75188 : Type) ->
       (B_75189 : Type) ->
         B_75189 ->
           (l_75191 : ((Nat_6) : Type)) ->
             ((PtsTo_18) l_75191) A_75188 -> ((PtsTo_18) l_75191) B_75189)::w
  Get :0
    ((A_75193 : Type) ->
       (l_75194 : ((Nat_6) : Type)) ->
         ((PtsTo_18) l_75194) A_75193 ->
           (FTensor_16 A_75193 fun __75196 => ((PtsTo_18) l_75194) A_75193))::w
  Free :0
    ((A_75197 : Type) ->
       (((fun A_75199 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_75200 => ((PtsTo_18) l_75200) A_75199)) :
          (A_75201 : Type) -> Linear))
         A_75197 -> Unit_2)::w
  New :0
    ((A_75202 : Type) ->
       A_75202 ->
         (((fun A_75204 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_75205 => ((PtsTo_18) l_75205) A_75204)) :
            (A_75206 : Type) -> Linear))
           A_75202)::w
  Ptr :0 ((A_75207 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  add :0 ((m_75210 : Nat_6) -> (n_75211 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_75212 : Type) ->
       (x_75213 : A_75212) ->
         (y_75214 : A_75212) ->
           (P_75215 : A_75212 -> Linear) ->
             (e_75217 : (Eq_0 A_75212 x_75213 y_75214)) ->
               (f_75218 : (P_75215) x_75213) -> (P_75215) y_75214)::w
  TyInd :0
    ((A_75219 : Type) ->
       (x_75220 : A_75219) ->
         (y_75221 : A_75219) ->
           (P_75222 : A_75219 -> Type) ->
             (e_75224 : (Eq_0 A_75219 x_75220 y_75221)) ->
               (f_75225 : (P_75222) x_75220) -> (P_75222) y_75221)::w
  Eq_sym :0
    ((A_75226 : Type) ->
       (x_75227 : A_75226) ->
         (y_75228 : A_75226) ->
           (e_75229 : (Eq_0 A_75226 x_75227 y_75228)) ->
             (Eq_0 A_75226 y_75228 x_75227))::w
  Eq_trans :0
    ((A_75230 : Type) ->
       (x_75231 : A_75230) ->
         (y_75232 : A_75230) ->
           (z_75233 : A_75230) ->
             (e1_75234 : (Eq_0 A_75230 x_75231 y_75232)) ->
               (e2_75235 : (Eq_0 A_75230 y_75232 z_75233)) ->
                 (Eq_0 A_75230 x_75231 z_75233))::w
}

tt_3

