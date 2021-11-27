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

Definition tpair2_38 :=
  ((fun A_39 B_40 x_41 y_42 => (tpair_15 x_41 y_42)) :
    (A_39 : Linear) ->
      (B_40 : Linear) -> A_39 -> B_40 >> (Tensor_14 A_39 B_40)).

Definition curryU_43 :=
  ((fun A_44 B_45 f_46 x_47 __0 => (f_46) x_47) :
    (A_44 : Linear) ->
      (B_45 : Type) -> A_44 -> B_45 -> A_44 -> Unit_2 >> B_45).

Inductive FTensor_16 (A_48 : Type) (F_49 : A_48 -> Linear) : Linear :=
| fpair_17 (A_48 : Type)
             (F_49 : A_48 -> Linear)
               : (x_51 : A_48) -> ((F_49) x_51) -> (FTensor_16 A_48 F_49).

Axiom unsafeC_52 : (A_54 : Linear) -> A_54 -> Unit_2.

Axiom unsafeP_55 : (A_57 : Linear) -> A_57.

Definition Loc_58 := ((Nat_6) : Type).

Axiom PtsTo_59 : Loc_58 -> Type -> Linear.

Definition Ptr_60 :=
  ((fun A_61 => (FTensor_16 Loc_58 fun l_62 => ((PtsTo_59) l_62) A_61)) :
    (A_61 : Type) -> Linear).

Axiom New_63 : (A_65 : Type) -> A_65 -> (Ptr_60) A_65.

Axiom Free_66 : (A_68 : Type) -> (Ptr_60) A_68 -> Unit_2.

Axiom Get_69 :
  (A_71 : Type) ->
    (l_73 : Loc_58) ->
      ((PtsTo_59) l_73) A_71 ->
        (FTensor_16 A_71 fun __0 => ((PtsTo_59) l_73) A_71).

Axiom Set_74 :
  (A_76 : Type) ->
    (B_78 : Type) ->
      B_78 ->
        (l_80 : Loc_58) -> ((PtsTo_59) l_80) A_76 -> ((PtsTo_59) l_80) B_78.

Inductive le_25 (n_81 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_81 : Nat_6) : (le_25 n_81 n_81)
| le_S_27 (n_81 : Nat_6)
            : (m_85 : Nat_6) ->
                ((le_25 n_81 m_85)) -> (le_25 n_81 (S_8 m_85)).

Definition lt_87 :=
  ((fun m_88 n_89 => (le_25 (S_8 m_88) n_89)) :
    (m_88 : Nat_6) -> (n_89 : Nat_6) -> Type).

Inductive ArrVec_28 (A_91 : Type) (l_92 : Loc_58) : (Nat_6) -> Linear :=
| Nil_29 (A_91 : Type) (l_92 : Loc_58) : (ArrVec_28 A_91 l_92 O_7)
| Cons_30 (A_91 : Type)
            (l_92 : Loc_58)
              : (n_96 : Nat_6) ->
                  (((PtsTo_59) ((add_29) l_92) n_96) A_91) ->
                    ((ArrVec_28 A_91 l_92 n_96)) ->
                      (ArrVec_28 A_91 l_92 (S_8 n_96)).

Definition Array_98 :=
  ((fun A_99 n_100 =>
      (FTensor_16 Loc_58 fun l_101 => (ArrVec_28 A_99 l_101 n_100))) :
    (A_99 : Type) -> (n_100 : Nat_6) -> Linear).

Definition nth_102 :=
  ((fix nth_102 A_103 l_104 m_105 n_106 pf_107 v_108 =>
      (match pf_107 in (le_25 __0 n_106) return
         (ArrVec_28 A_103 l_104 n_106) ->
           (Tensor_14
             ((PtsTo_59) ((add_29) l_104) m_105) A_103
               ((PtsTo_59) ((add_29) l_104) m_105) A_103 >>
                 (ArrVec_28 A_103 l_104 n_106))
       with
       | (le_n_26 ) =>
         fun v_108 =>
           (match v_108 in (ArrVec_28 __0 __0 n_106) return
              match n_106 with
              | (O_7 ) => Base_4
              | (S_8 n0_109) =>
                (Eq_0 Nat_6 m_105 n0_109) >>
                  (Tensor_14
                    ((PtsTo_59) ((add_29) l_104) n0_109) A_103
                      ((PtsTo_59) ((add_29) l_104) n0_109) A_103 >>
                        (ArrVec_28 A_103 l_104 n_106))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_106 c_110 v_108) =>
              fun __0 =>
                (tpair_15 c_110 fun c_110 => (Cons_30 n_106 c_110 v_108))
            end) refl_1
       | (le_S_27 __0 pf_107) =>
         fun v_108 =>
           (match v_108 in (ArrVec_28 __0 __0 n_106) return
              match n_106 with
              | (O_7 ) => Base_4
              | (S_8 n0_111) =>
                ((lt_87) m_105) n0_111 >>
                  (Tensor_14
                    ((PtsTo_59) ((add_29) l_104) m_105) A_103
                      ((PtsTo_59) ((add_29) l_104) m_105) A_103 >>
                        (ArrVec_28 A_103 l_104 n_106))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_106 c0_112 v0_113) =>
              fun pf_107 =>
                let (tpair_15 c_114 f_115) :=
                  ((((((nth_102) A_103) l_104) m_105) n_106) pf_107) v0_113
                in
                (tpair_15 c_114
                            fun c_114 => (Cons_30 n_106 c0_112 (f_115) c_114))
            end) pf_107
       end) v_108) :
    (A_103 : Type) ->
      (l_104 : Nat_6) ->
        (m_105 : Nat_6) ->
          (n_106 : Nat_6) ->
            (pf_107 : ((lt_87) m_105) n_106) ->
              (v_108 : (ArrVec_28 A_103 l_104 n_106)) ->
                (Tensor_14
                  ((PtsTo_59) ((add_29) l_104) m_105) A_103
                    ((PtsTo_59) ((add_29) l_104) m_105) A_103 >>
                      (ArrVec_28 A_103 l_104 n_106))).

Definition index_116 :=
  ((fun A_117 m_118 n_119 pf_120 a_121 =>
      let (fpair_17 l_123 v_124) := a_121 in
      let (tpair_15 c_125 f_126) :=
        ((((((nth_102) A_117) l_123) m_118) n_119) pf_120) v_124
      in
      let (fpair_17 x_128 c_125) :=
        (((Get_69) A_117) ((add_29) l_123) m_118) c_125
      in (fpair_17 x_128 (fpair_17 l_123 (f_126) c_125))) :
    (A_117 : Type) ->
      (m_118 : Nat_6) ->
        (n_119 : Nat_6) ->
          (pf_120 : ((lt_87) m_118) n_119) ->
            (a_121 : ((Array_98) A_117) n_119) ->
              (FTensor_16 A_117 fun __0 => ((Array_98) A_117) n_119)).

Definition Just0_129 :=
  (((Sigma_12 Nat_6 fun x_130 => (Eq_0 Nat_6 x_130 O_7))) : Type).

Definition silly_131 :=
  ((fun m_132 n_133 pf_134 a_135 =>
      let (fpair_17 x_pf_137 a_135) :=
        (((((index_116) Just0_129) m_132) n_133) pf_134) a_135
      in
      let (fpair_17 y_pf_139 a_135) :=
        (((((index_116) Just0_129) m_132) n_133) pf_134) a_135
      in
      let (pair_13 x_140 pf1_141) := x_pf_137 in
      let (pair_13 y_142 pf2_143) := y_pf_139 in
      let pf2_143 := ((((Eq_sym_10) Nat_6) y_142) O_7) pf2_143 in
      let pf_134 :=
        ((((((((Eq_trans_3) Nat_6) x_140) O_7) y_142) pf1_141) pf2_143) :
          (Eq_0 Nat_6 x_140 y_142))
      in a_135) :
    (m_132 : Nat_6) ->
      (n_133 : Nat_6) ->
        (pf_134 : ((lt_87) m_132) n_133) ->
          (a_135 : ((Array_98) Just0_129) n_133) ->
            ((Array_98) Just0_129) n_133).

Definition main_144 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_278 : Type) (x_279 : A_278) : (A_278) -> Type :=
| refl_1 (A_281 : Type) (x_282 : A_281) : (Eq_0 A_281 x_282 x_282).

Definition Eq_trans_283 :=
  ((fun A_284 x_285 y_286 z_287 e1_288 e2_289 =>
      match e2_289 in (Eq_0 __291 __292 y_293) return
        (Eq_0 A_284 x_285 y_293)
      with
      | (refl_1 ) => e1_288
      end) :
    (A_294 : Type) ->
      (x_295 : A_294) ->
        (y_296 : A_294) ->
          (z_297 : A_294) ->
            (e1_298 : (Eq_0 A_294 x_295 y_296)) ->
              (e2_299 : (Eq_0 A_294 y_296 z_297)) -> (Eq_0 A_294 x_295 z_297)).

Definition Eq_sym_300 :=
  ((fun A_301 x_302 y_303 e_304 =>
      match e_304 in (Eq_0 __306 __307 y_308) return (Eq_0 A_301 y_308 x_302)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_309 : Type) ->
      (x_310 : A_309) ->
        (y_311 : A_309) ->
          (e_312 : (Eq_0 A_309 x_310 y_311)) -> (Eq_0 A_309 y_311 x_310)).

Definition TyInd_313 :=
  ((fun A_314 x_315 y_316 P_317 e_318 f_319 =>
      match e_318 in (Eq_0 __321 __322 y_323) return (P_317) y_323 with
      | (refl_1 ) => f_319
      end) :
    (A_324 : Type) ->
      (x_325 : A_324) ->
        (y_326 : A_324) ->
          (P_327 : A_324 -> Type) ->
            (e_329 : (Eq_0 A_324 x_325 y_326)) ->
              (f_330 : (P_327) x_325) -> (P_327) y_326).

Definition LnInd_331 :=
  ((fun A_332 x_333 y_334 P_335 e_336 f_337 =>
      match e_336 in (Eq_0 __339 __340 y_341) return (P_335) y_341 with
      | (refl_1 ) => f_337
      end) :
    (A_342 : Type) ->
      (x_343 : A_342) ->
        (y_344 : A_342) ->
          (P_345 : A_342 -> Linear) ->
            (e_347 : (Eq_0 A_342 x_343 y_344)) ->
              (f_348 : (P_345) x_343) -> (P_345) y_344).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_350 :=
  ((fix add_351 m_352 n_353 =>
      match m_352 with
      | (O_7 ) => n_353
      | (S_8 m_354) => (S_8 ((add_351) m_354) n_353)
      end) :
    (m_355 : Nat_6) -> (n_356 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_357 : Type) (F_358 : A_357 -> Type) : Type :=
| pair_13 (A_360 : Type)
            (F_361 : A_360 -> Type)
              : (x_363 : A_360) -> ((F_361) x_363) -> (Sigma_12 A_360 F_361).

Inductive Tensor_14 (A_365 : Linear) (B_366 : Linear) : Linear :=
| tpair_15 (A_367 : Linear)
             (B_368 : Linear) : (A_367) -> (B_368) -> (Tensor_14 A_367 B_368).

Definition tpair2_371 :=
  ((fun A_372 B_373 x_374 y_375 => (tpair_15 x_374 y_375)) :
    (A_376 : Linear) ->
      (B_377 : Linear) -> A_376 -> B_377 >> (Tensor_14 A_376 B_377)).

Definition curryU_380 :=
  ((fun A_381 B_382 f_383 x_384 __385 => (f_383) x_384) :
    (A_386 : Linear) ->
      (B_387 : Type) -> A_386 -> B_387 -> A_386 -> Unit_2 >> B_387).

Inductive FTensor_16 (A_392 : Type) (F_393 : A_392 -> Linear) : Linear :=
| fpair_17 (A_395 : Type)
             (F_396 : A_395 -> Linear)
               : (x_398 : A_395) ->
                   ((F_396) x_398) -> (FTensor_16 A_395 F_396).

Axiom unsafeC_400 : (A_401 : Linear) -> A_401 -> Unit_2.

Axiom unsafeP_403 : (A_404 : Linear) -> A_404.

Definition Loc_405 := ((Nat_6) : Type).

Axiom PtsTo_406 : Loc_405 -> Type -> Linear.

Definition Ptr_409 :=
  ((fun A_410 => (FTensor_16 Loc_405 fun l_411 => ((PtsTo_406) l_411) A_410)) :
    (A_412 : Type) -> Linear).

Axiom New_413 : (A_414 : Type) -> A_414 -> (Ptr_409) A_414.

Axiom Free_416 : (A_417 : Type) -> (Ptr_409) A_417 -> Unit_2.

Axiom Get_419 :
  (A_420 : Type) ->
    (l_421 : Loc_405) ->
      ((PtsTo_406) l_421) A_420 ->
        (FTensor_16 A_420 fun __423 => ((PtsTo_406) l_421) A_420).

Axiom Set_424 :
  (A_425 : Type) ->
    (B_426 : Type) ->
      B_426 ->
        (l_428 : Loc_405) ->
          ((PtsTo_406) l_428) A_425 -> ((PtsTo_406) l_428) B_426.

Inductive le_25 (n_430 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_432 : Nat_6) : (le_25 n_432 n_432)
| le_S_27 (n_433 : Nat_6)
            : (m_434 : Nat_6) ->
                ((le_25 n_433 m_434)) -> (le_25 n_433 (S_8 m_434)).

Definition lt_436 :=
  ((fun m_437 n_438 => (le_25 (S_8 m_437) n_438)) :
    (m_439 : Nat_6) -> (n_440 : Nat_6) -> Type).

Inductive ArrVec_28 (A_441 : Type) (l_442 : Loc_405) : (Nat_6) -> Linear :=
| Nil_29 (A_444 : Type) (l_445 : Loc_405) : (ArrVec_28 A_444 l_445 O_7)
| Cons_30 (A_446 : Type)
            (l_447 : Loc_405)
              : (n_448 : Nat_6) ->
                  (((PtsTo_406) ((add_350) l_447) n_448) A_446) ->
                    ((ArrVec_28 A_446 l_447 n_448)) ->
                      (ArrVec_28 A_446 l_447 (S_8 n_448)).

Definition Array_451 :=
  ((fun A_452 n_453 =>
      (FTensor_16 Loc_405 fun l_454 => (ArrVec_28 A_452 l_454 n_453))) :
    (A_455 : Type) -> (n_456 : Nat_6) -> Linear).

Definition nth_457 :=
  ((fix nth_458 A_459 l_460 m_461 n_462 pf_463 v_464 =>
      (match pf_463 in (le_25 __466 n_467) return
         (ArrVec_28 A_459 l_460 n_467) ->
           (Tensor_14
             ((PtsTo_406) ((add_350) l_460) m_461) A_459
               ((PtsTo_406) ((add_350) l_460) m_461) A_459 >>
                 (ArrVec_28 A_459 l_460 n_467))
       with
       | (le_n_26 ) =>
         fun v_470 =>
           (match v_470 in (ArrVec_28 __472 __473 n_474) return
              match n_474 with
              | (O_7 ) => Base_4
              | (S_8 n0_475) =>
                (Eq_0 Nat_6 m_461 n0_475) >>
                  (Tensor_14
                    ((PtsTo_406) ((add_350) l_460) n0_475) A_459
                      ((PtsTo_406) ((add_350) l_460) n0_475) A_459 >>
                        (ArrVec_28 A_459 l_460 n_474))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_478 c_479 v_480) =>
              fun __481 =>
                (tpair_15 c_479 fun c_482 => (Cons_30 n_478 c_482 v_480))
            end) refl_1
       | (le_S_27 __483 pf_484) =>
         fun v_485 =>
           (match v_485 in (ArrVec_28 __487 __488 n_489) return
              match n_489 with
              | (O_7 ) => Base_4
              | (S_8 n0_490) =>
                ((lt_436) m_461) n0_490 >>
                  (Tensor_14
                    ((PtsTo_406) ((add_350) l_460) m_461) A_459
                      ((PtsTo_406) ((add_350) l_460) m_461) A_459 >>
                        (ArrVec_28 A_459 l_460 n_489))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_493 c0_494 v0_495) =>
              fun pf_496 =>
                let x_497 :=
                  ((((((nth_458) A_459) l_460) m_461) n_493) pf_496) v0_495
                in
                match x_497 with
                | (tpair_15 c_498 f_499) =>
                  (tpair_15 c_498
                              fun c_500 =>
                                (Cons_30 n_493 c0_494 (f_499) c_500))
                end
            end) pf_484
       end) v_464) :
    (A_501 : Type) ->
      (l_502 : Nat_6) ->
        (m_503 : Nat_6) ->
          (n_504 : Nat_6) ->
            (pf_505 : ((lt_436) m_503) n_504) ->
              (v_506 : (ArrVec_28 A_501 l_502 n_504)) ->
                (Tensor_14
                  ((PtsTo_406) ((add_350) l_502) m_503) A_501
                    ((PtsTo_406) ((add_350) l_502) m_503) A_501 >>
                      (ArrVec_28 A_501 l_502 n_504))).

Definition index_508 :=
  ((fun A_509 m_510 n_511 pf_512 a_513 =>
      let x_514 := a_513 in
      match x_514 with
      | (fpair_17 l_515 v_516) =>
        let x_517 := ((((((nth_457) A_509) l_515) m_510) n_511) pf_512) v_516
        in
        match x_517 with
        | (tpair_15 c_518 f_519) =>
          let x_520 := (((Get_419) A_509) ((add_350) l_515) m_510) c_518 in
          match x_520 with
          | (fpair_17 x_521 c_522) =>
            (fpair_17 x_521 (fpair_17 l_515 (f_519) c_522))
          end
        end
      end) :
    (A_523 : Type) ->
      (m_524 : Nat_6) ->
        (n_525 : Nat_6) ->
          (pf_526 : ((lt_436) m_524) n_525) ->
            (a_527 : ((Array_451) A_523) n_525) ->
              (FTensor_16 A_523 fun __528 => ((Array_451) A_523) n_525)).

Definition Just0_529 :=
  (((Sigma_12 Nat_6 fun x_530 => (Eq_0 Nat_6 x_530 O_7))) : Type).

Definition silly_531 :=
  ((fun m_532 n_533 pf_534 a_535 =>
      let x_536 := (((((index_508) Just0_529) m_532) n_533) pf_534) a_535 in
      match x_536 with
      | (fpair_17 x_pf_537 a_538) =>
        let x_539 := (((((index_508) Just0_529) m_532) n_533) pf_534) a_538
        in
        match x_539 with
        | (fpair_17 y_pf_540 a_541) =>
          let x_542 := x_pf_537 in
          match x_542 with
          | (pair_13 x_543 pf1_544) =>
            let x0_545 := y_pf_540 in
            match x0_545 with
            | (pair_13 y_546 pf2_547) =>
              let pf2_548 := ((((Eq_sym_300) Nat_6) y_546) O_7) pf2_547 in
              let pf_549 :=
                ((((((((Eq_trans_283) Nat_6) x_543) O_7) y_546) pf1_544)
                    pf2_548) :
                  (Eq_0 Nat_6 x_543 y_546))
              in a_541
            end
          end
        end
      end) :
    (m_550 : Nat_6) ->
      (n_551 : Nat_6) ->
        (pf_552 : ((lt_436) m_550) n_551) ->
          (a_553 : ((Array_451) Just0_529) n_551) ->
            ((Array_451) Just0_529) n_551).

Definition main_554 := ((tt_3) : Unit_2).



v_ctx  := {
  main :0 (Unit_2)::w
  silly :0
    ((m_82849 : Nat_6) ->
       (n_82850 : Nat_6) ->
         (pf_82851 :
           ((((fun m_82852 n_82853 => (le_25 (S_8 m_82852) n_82853)) :
               (m_82854 : Nat_6) -> (n_82855 : Nat_6) -> Type))
              m_82849)
             n_82850) ->
           (a_82856 :
             ((((fun A_82857 n_82858 =>
                   (FTensor_16
                     ((Nat_6) : Type)
                       fun l_82859 => (ArrVec_28 A_82857 l_82859 n_82858))) :
                 (A_82860 : Type) -> (n_82861 : Nat_6) -> Linear))
                (((Sigma_12 Nat_6 fun x_82862 => (Eq_0 Nat_6 x_82862 O_7))) :
                  Type))
               n_82850) ->
             ((((fun A_82863 n_82864 =>
                   (FTensor_16
                     ((Nat_6) : Type)
                       fun l_82865 => (ArrVec_28 A_82863 l_82865 n_82864))) :
                 (A_82866 : Type) -> (n_82867 : Nat_6) -> Linear))
                (((Sigma_12 Nat_6 fun x_82868 => (Eq_0 Nat_6 x_82868 O_7))) :
                  Type))
               n_82850)::w
  Just0 :0 (Type)::w
  index :0
    ((A_82869 : Type) ->
       (m_82870 : Nat_6) ->
         (n_82871 : Nat_6) ->
           (pf_82872 :
             ((((fun m_82873 n_82874 => (le_25 (S_8 m_82873) n_82874)) :
                 (m_82875 : Nat_6) -> (n_82876 : Nat_6) -> Type))
                m_82870)
               n_82871) ->
             (a_82877 :
               ((((fun A_82878 n_82879 =>
                     (FTensor_16
                       ((Nat_6) : Type)
                         fun l_82880 => (ArrVec_28 A_82878 l_82880 n_82879))) :
                   (A_82881 : Type) -> (n_82882 : Nat_6) -> Linear))
                  A_82869)
                 n_82871) ->
               (FTensor_16
                 A_82869
                   fun __82883 =>
                     ((((fun A_82884 n_82885 =>
                           (FTensor_16
                             ((Nat_6) : Type)
                               fun l_82886 =>
                                 (ArrVec_28 A_82884 l_82886 n_82885))) :
                         (A_82887 : Type) -> (n_82888 : Nat_6) -> Linear))
                        A_82869)
                       n_82871))::w
  nth :0
    ((A_82889 : Type) ->
       (l_82890 : Nat_6) ->
         (m_82891 : Nat_6) ->
           (n_82892 : Nat_6) ->
             (pf_82893 :
               ((((fun m_82894 n_82895 => (le_25 (S_8 m_82894) n_82895)) :
                   (m_82896 : Nat_6) -> (n_82897 : Nat_6) -> Type))
                  m_82891)
                 n_82892) ->
               (v_82898 : (ArrVec_28 A_82889 l_82890 n_82892)) ->
                 (Tensor_14
                   ((PtsTo_20)
                      ((((fix add_82899 m_82900 n_82901 =>
                            match m_82900 with
                            | (O_7 ) => n_82901
                            | (S_8 m_82902) =>
                              (S_8 ((add_82899) m_82902) n_82901)
                            end) :
                          (m_82903 : Nat_6) -> (n_82904 : Nat_6) -> Nat_6))
                         l_82890)
                        m_82891)
                     A_82889
                     ((PtsTo_20)
                        ((((fix add_82906 m_82907 n_82908 =>
                              match m_82907 with
                              | (O_7 ) => n_82908
                              | (S_8 m_82909) =>
                                (S_8 ((add_82906) m_82909) n_82908)
                              end) :
                            (m_82910 : Nat_6) -> (n_82911 : Nat_6) -> Nat_6))
                           l_82890)
                          m_82891)
                       A_82889 >> (ArrVec_28 A_82889 l_82890 n_82892)))::w
  Array :0 ((A_82912 : Type) -> (n_82913 : Nat_6) -> Linear)::w
  lt :0 ((m_82914 : Nat_6) -> (n_82915 : Nat_6) -> Type)::w
  Set :0
    ((A_82916 : Type) ->
       (B_82917 : Type) ->
         B_82917 ->
           (l_82919 : ((Nat_6) : Type)) ->
             ((PtsTo_20) l_82919) A_82916 -> ((PtsTo_20) l_82919) B_82917)::w
  Get :0
    ((A_82921 : Type) ->
       (l_82922 : ((Nat_6) : Type)) ->
         ((PtsTo_20) l_82922) A_82921 ->
           (FTensor_16 A_82921 fun __82924 => ((PtsTo_20) l_82922) A_82921))::w
  Free :0
    ((A_82925 : Type) ->
       (((fun A_82927 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_82928 => ((PtsTo_20) l_82928) A_82927)) :
          (A_82929 : Type) -> Linear))
         A_82925 -> Unit_2)::w
  New :0
    ((A_82930 : Type) ->
       A_82930 ->
         (((fun A_82932 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_82933 => ((PtsTo_20) l_82933) A_82932)) :
            (A_82934 : Type) -> Linear))
           A_82930)::w
  Ptr :0 ((A_82935 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  unsafeP :0 ((A_82938 : Linear) -> A_82938)::w
  unsafeC :0 ((A_82939 : Linear) -> A_82939 -> Unit_2)::w
  curryU :0
    ((A_82941 : Linear) ->
       (B_82942 : Type) -> A_82941 -> B_82942 -> A_82941 -> Unit_2 >> B_82942)::w
  tpair2 :0
    ((A_82947 : Linear) ->
       (B_82948 : Linear) ->
         A_82947 -> B_82948 >> (Tensor_14 A_82947 B_82948))::w
  add :0 ((m_82951 : Nat_6) -> (n_82952 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_82953 : Type) ->
       (x_82954 : A_82953) ->
         (y_82955 : A_82953) ->
           (P_82956 : A_82953 -> Linear) ->
             (e_82958 : (Eq_0 A_82953 x_82954 y_82955)) ->
               (f_82959 : (P_82956) x_82954) -> (P_82956) y_82955)::w
  TyInd :0
    ((A_82960 : Type) ->
       (x_82961 : A_82960) ->
         (y_82962 : A_82960) ->
           (P_82963 : A_82960 -> Type) ->
             (e_82965 : (Eq_0 A_82960 x_82961 y_82962)) ->
               (f_82966 : (P_82963) x_82961) -> (P_82963) y_82962)::w
  Eq_sym :0
    ((A_82967 : Type) ->
       (x_82968 : A_82967) ->
         (y_82969 : A_82967) ->
           (e_82970 : (Eq_0 A_82967 x_82968 y_82969)) ->
             (Eq_0 A_82967 y_82969 x_82968))::w
  Eq_trans :0
    ((A_82971 : Type) ->
       (x_82972 : A_82971) ->
         (y_82973 : A_82971) ->
           (z_82974 : A_82971) ->
             (e1_82975 : (Eq_0 A_82971 x_82972 y_82973)) ->
               (e2_82976 : (Eq_0 A_82971 y_82973 z_82974)) ->
                 (Eq_0 A_82971 x_82972 z_82974))::w
}

tt_3

