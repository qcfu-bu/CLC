parse ok
desugar ok
elab ok
resolve ok
tcheck ok
--------------------------------------------------------------------------------
Inductive Eq_0 (A_33305 : Type) (x_33306 : A_33305) : (A_33305) -> Type :=
| refl_1 (A_33308 : Type)
           (x_33309 : A_33308) : (Eq_0 A_33308 x_33309 x_33309).

Definition Eq_trans_33310 :=
  ((fun A_33311 x_33312 y_33313 z_33314 e1_33315 e2_33316 =>
      match e2_33316 in (Eq_0 __33318 __33319 y_33320) return
        (Eq_0 A_33311 x_33312 y_33320)
      with
      | (refl_1 ) => e1_33315
      end) :
    (A_33321 : Type) ->
      (x_33322 : A_33321) ->
        (y_33323 : A_33321) ->
          (z_33324 : A_33321) ->
            (e1_33325 : (Eq_0 A_33321 x_33322 y_33323)) ->
              (e2_33326 : (Eq_0 A_33321 y_33323 z_33324)) ->
                (Eq_0 A_33321 x_33322 z_33324)).

Definition Eq_sym_33327 :=
  ((fun A_33328 x_33329 y_33330 e_33331 =>
      match e_33331 in (Eq_0 __33333 __33334 y_33335) return
        (Eq_0 A_33328 y_33335 x_33329)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_33336 : Type) ->
      (x_33337 : A_33336) ->
        (y_33338 : A_33336) ->
          (e_33339 : (Eq_0 A_33336 x_33337 y_33338)) ->
            (Eq_0 A_33336 y_33338 x_33337)).

Definition TyInd_33340 :=
  ((fun A_33341 x_33342 y_33343 P_33344 e_33345 f_33346 =>
      match e_33345 in (Eq_0 __33348 __33349 y_33350) return
        (P_33344) y_33350
      with
      | (refl_1 ) => f_33346
      end) :
    (A_33351 : Type) ->
      (x_33352 : A_33351) ->
        (y_33353 : A_33351) ->
          (P_33354 : (A_33351) -> Type) ->
            (e_33356 : (Eq_0 A_33351 x_33352 y_33353)) ->
              (f_33357 : (P_33354) x_33352) -> (P_33354) y_33353).

Definition LnInd_33358 :=
  ((fun A_33359 x_33360 y_33361 P_33362 e_33363 f_33364 =>
      match e_33363 in (Eq_0 __33366 __33367 y_33368) return
        (P_33362) y_33368
      with
      | (refl_1 ) => f_33364
      end) :
    (A_33369 : Type) ->
      (x_33370 : A_33369) ->
        (y_33371 : A_33369) ->
          (P_33372 : (A_33369) -> Linear) ->
            (e_33374 : (Eq_0 A_33369 x_33370 y_33371)) ->
              (f_33375 : (P_33372) x_33370) -> (P_33372) y_33371).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_33377 :=
  ((fix add_33378 m_33379 n_33380 =>
      match m_33379 with
      | (O_7 ) => n_33380
      | (S_8 m_33381) => (S_8 ((add_33378) m_33381) n_33380)
      end) :
    (m_33382 : Nat_6) -> (n_33383 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_33384 : Type) (F_33385 : (A_33384) -> Type) : Type :=
| pair_13 (A_33387 : Type)
            (F_33388 : (A_33387) -> Type)
              : (x_33390 : A_33387) ->
                  ((F_33388) x_33390) -> (Sigma_12 A_33387 F_33388).

Inductive Tensor_14 (A_33392 : Linear) (B_33393 : Linear) : Linear :=
| tpair_15 (A_33394 : Linear)
             (B_33395 : Linear)
               : (A_33394) -> (B_33395) -> (Tensor_14 A_33394 B_33395).

Inductive FTensor_16 (A_33398 : Type)
                       (F_33399 : (A_33398) -> Linear) : Linear :=
| fpair_17 (A_33401 : Type)
             (F_33402 : (A_33401) -> Linear)
               : (x_33404 : A_33401) ->
                   ((F_33402) x_33404) -> (FTensor_16 A_33401 F_33402).

Axiom unsafeC_33406 : (A_33407 : Linear) -> (A_33407) -> Unit_2.

Axiom unsafeP_33409 : (A_33410 : Linear) -> A_33410.

Definition Loc_33411 := ((Nat_6) : Type).

Axiom PtsTo_33412 : (Loc_33411) -> (Type) -> Linear.

Definition Ptr_33415 :=
  ((fun A_33416 =>
      (FTensor_16 Loc_33411 fun l_33417 => ((PtsTo_33412) l_33417) A_33416)) :
    (A_33418 : Type) -> Linear).

Axiom New_33419 : (A_33420 : Type) -> (A_33420) -> (Ptr_33415) A_33420.

Axiom Free_33422 : (A_33423 : Type) -> ((Ptr_33415) A_33423) -> Unit_2.

Axiom Get_33425 :
  (A_33426 : Type) ->
    (l_33427 : Loc_33411) ->
      (((PtsTo_33412) l_33427) A_33426) ->
        (FTensor_16 A_33426 fun __33429 => ((PtsTo_33412) l_33427) A_33426).

Axiom Set_33430 :
  (A_33431 : Type) ->
    (B_33432 : Type) ->
      (B_33432) ->
        (l_33434 : Loc_33411) ->
          (((PtsTo_33412) l_33434) A_33431) ->
            ((PtsTo_33412) l_33434) B_33432.

Inductive le_25 (n_33436 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_33438 : Nat_6) : (le_25 n_33438 n_33438)
| le_S_27 (n_33439 : Nat_6)
            : (m_33440 : Nat_6) ->
                ((le_25 n_33439 m_33440)) -> (le_25 n_33439 (S_8 m_33440)).

Definition lt_33442 :=
  ((fun m_33443 n_33444 => (le_25 (S_8 m_33443) n_33444)) :
    (m_33445 : Nat_6) -> (n_33446 : Nat_6) -> Type).

Inductive ArrVec_28 (A_33447 : Type)
                      (l_33448 : Loc_33411) : (Nat_6) -> Linear :=
| Nil_29 (A_33450 : Type)
           (l_33451 : Loc_33411) : (ArrVec_28 A_33450 l_33451 O_7)
| Cons_30 (A_33452 : Type)
            (l_33453 : Loc_33411)
              : (n_33454 : Nat_6) ->
                  (((PtsTo_33412) ((add_33377) l_33453) n_33454) A_33452) ->
                    ((ArrVec_28 A_33452 l_33453 n_33454)) ->
                      (ArrVec_28 A_33452 l_33453 (S_8 n_33454)).

Definition Array_33457 :=
  ((fun A_33458 n_33459 =>
      (FTensor_16
        Loc_33411 fun l_33460 => (ArrVec_28 A_33458 l_33460 n_33459))) :
    (A_33461 : Type) -> (n_33462 : Nat_6) -> Linear).

Definition nth_33463 :=
  ((fix nth_33464 A_33465 l_33466 m_33467 n_33468 pf_33469 v_33470 =>
      (match pf_33469 in (le_25 __33472 n_33473) return
         ((ArrVec_28 A_33465 l_33466 n_33473)) ->
           (Tensor_14
             ((PtsTo_33412) ((add_33377) l_33466) m_33467) A_33465
               (((PtsTo_33412) ((add_33377) l_33466) m_33467) A_33465) >>
                 (ArrVec_28 A_33465 l_33466 n_33473))
       with
       | (le_n_26 ) =>
         fun v_33476 =>
           (match v_33476 in (ArrVec_28 __33478 __33479 n_33480) return
              match n_33480 with
              | (O_7 ) => Base_4
              | (S_8 n0_33481) =>
                ((Eq_0 Nat_6 m_33467 n0_33481)) >>
                  (Tensor_14
                    ((PtsTo_33412) ((add_33377) l_33466) n0_33481) A_33465
                      (((PtsTo_33412) ((add_33377) l_33466) n0_33481) A_33465) >>
                        (ArrVec_28 A_33465 l_33466 n_33480))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_33484 c_33485 v_33486) =>
              fun __33487 =>
                (tpair_15 c_33485
                            fun c_33488 => (Cons_30 n_33484 c_33488 v_33486))
            end) refl_1
       | (le_S_27 __33489 pf_33490) =>
         fun v_33491 =>
           (match v_33491 in (ArrVec_28 __33493 __33494 n_33495) return
              match n_33495 with
              | (O_7 ) => Base_4
              | (S_8 n0_33496) =>
                (((lt_33442) m_33467) n0_33496) >>
                  (Tensor_14
                    ((PtsTo_33412) ((add_33377) l_33466) m_33467) A_33465
                      (((PtsTo_33412) ((add_33377) l_33466) m_33467) A_33465) >>
                        (ArrVec_28 A_33465 l_33466 n_33495))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_33499 c0_33500 v0_33501) =>
              fun pf_33502 =>
                let x_33503 :=
                  ((((((nth_33464) A_33465) l_33466) m_33467) n_33499)
                     pf_33502)
                    v0_33501
                in
                match x_33503 with
                | (tpair_15 c_33504 f_33505) =>
                  (tpair_15 c_33504
                              fun c_33506 =>
                                (Cons_30 n_33499 c0_33500 (f_33505) c_33506))
                end
            end) pf_33490
       end) v_33470) :
    (A_33507 : Type) ->
      (l_33508 : Nat_6) ->
        (m_33509 : Nat_6) ->
          (n_33510 : Nat_6) ->
            (pf_33511 : ((lt_33442) m_33509) n_33510) ->
              (v_33512 : (ArrVec_28 A_33507 l_33508 n_33510)) ->
                (Tensor_14
                  ((PtsTo_33412) ((add_33377) l_33508) m_33509) A_33507
                    (((PtsTo_33412) ((add_33377) l_33508) m_33509) A_33507) >>
                      (ArrVec_28 A_33507 l_33508 n_33510))).

Definition index_33514 :=
  ((fun A_33515 m_33516 n_33517 pf_33518 a_33519 =>
      let x_33520 := a_33519 in
      match x_33520 with
      | (fpair_17 l_33521 v_33522) =>
        let x_33523 :=
          ((((((nth_33463) A_33515) l_33521) m_33516) n_33517) pf_33518)
            v_33522
        in
        match x_33523 with
        | (tpair_15 c_33524 f_33525) =>
          let x_33526 :=
            (((Get_33425) A_33515) ((add_33377) l_33521) m_33516) c_33524
          in
          match x_33526 with
          | (fpair_17 x_33527 c_33528) =>
            (fpair_17 x_33527 (fpair_17 l_33521 (f_33525) c_33528))
          end
        end
      end) :
    (A_33529 : Type) ->
      (m_33530 : Nat_6) ->
        (n_33531 : Nat_6) ->
          (pf_33532 : ((lt_33442) m_33530) n_33531) ->
            (a_33533 : ((Array_33457) A_33529) n_33531) ->
              (FTensor_16
                A_33529 fun __33534 => ((Array_33457) A_33529) n_33531)).

Definition Just0_33535 :=
  (((Sigma_12 Nat_6 fun x_33536 => (Eq_0 Nat_6 x_33536 O_7))) : Type).

Definition silly_33537 :=
  ((fun m_33538 n_33539 pf_33540 a_33541 =>
      let x_33542 :=
        (((((index_33514)
              (Sigma_12 Nat_6 fun x_33543 => (Eq_0 Nat_6 x_33543 O_7)))
             m_33538)
            n_33539)
           pf_33540)
          a_33541
      in
      match x_33542 with
      | (fpair_17 x_pf_33544 a_33545) =>
        let x_33546 :=
          (((((index_33514)
                (Sigma_12 Nat_6 fun x_33547 => (Eq_0 Nat_6 x_33547 O_7)))
               m_33538)
              n_33539)
             pf_33540)
            a_33545
        in
        match x_33546 with
        | (fpair_17 y_pf_33548 a_33549) =>
          let x_33550 := x_pf_33544 in
          match x_33550 with
          | (pair_13 x_33551 pf1_33552) =>
            let x0_33553 := y_pf_33548 in
            match x0_33553 with
            | (pair_13 y_33554 pf2_33555) =>
              let pf2_33556 :=
                ((((Eq_sym_33327) Nat_6) y_33554) O_7) pf2_33555
              in
              let pf_33557 :=
                ((((((((Eq_trans_33310) Nat_6) x_33551) O_7) y_33554)
                     pf1_33552)
                    pf2_33556) :
                  (Eq_0 Nat_6 x_33551 y_33554))
              in a_33549
            end
          end
        end
      end) :
    (m_33558 : Nat_6) ->
      (n_33559 : Nat_6) ->
        (pf_33560 : ((lt_33442) m_33558) n_33559) ->
          (a_33561 : ((Array_33457) Just0_33535) n_33559) ->
            ((Array_33457) Just0_33535) n_33559).

Definition main_33562 := ((tt_3) : Unit_2).


--------------------------------------------------------------------------------
tt_3
