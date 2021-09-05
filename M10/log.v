parse ok
desugar ok
elab ok
resolve ok
tcheck ok
Inductive Eq_0 (A_18327 : Type) (x_18328 : A_18327) : (A_18327) -> Type :=
| refl_1 (A_18330 : Type)
           (x_18331 : A_18330) : (Eq_0 A_18330 x_18331 x_18331).

Definition Eq_trans_18332 :=
  ((fun A_18333 x_18334 y_18335 z_18336 e1_18337 e2_18338 =>
      match e2_18338 in (Eq_0 __18340 __18341 y_18342) return
        (Eq_0 A_18333 x_18334 y_18342)
      with
      | (refl_1 ) => e1_18337
      end) :
    (A_18343 : Type) ->
      (x_18344 : A_18343) ->
        (y_18345 : A_18343) ->
          (z_18346 : A_18343) ->
            (e1_18347 : (Eq_0 A_18343 x_18344 y_18345)) ->
              (e2_18348 : (Eq_0 A_18343 y_18345 z_18346)) ->
                (Eq_0 A_18343 x_18344 z_18346)).

Definition Eq_sym_18349 :=
  ((fun A_18350 x_18351 y_18352 e_18353 =>
      match e_18353 in (Eq_0 __18355 __18356 y_18357) return
        (Eq_0 A_18350 y_18357 x_18351)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_18358 : Type) ->
      (x_18359 : A_18358) ->
        (y_18360 : A_18358) ->
          (e_18361 : (Eq_0 A_18358 x_18359 y_18360)) ->
            (Eq_0 A_18358 y_18360 x_18359)).

Definition TyInd_18362 :=
  ((fun A_18363 x_18364 y_18365 P_18366 e_18367 f_18368 =>
      match e_18367 in (Eq_0 __18370 __18371 y_18372) return
        (P_18366) y_18372
      with
      | (refl_1 ) => f_18368
      end) :
    (A_18373 : Type) ->
      (x_18374 : A_18373) ->
        (y_18375 : A_18373) ->
          (P_18376 : (A_18373) -> Type) ->
            (e_18378 : (Eq_0 A_18373 x_18374 y_18375)) ->
              (f_18379 : (P_18376) x_18374) -> (P_18376) y_18375).

Definition LnInd_18380 :=
  ((fun A_18381 x_18382 y_18383 P_18384 e_18385 f_18386 =>
      match e_18385 in (Eq_0 __18388 __18389 y_18390) return
        (P_18384) y_18390
      with
      | (refl_1 ) => f_18386
      end) :
    (A_18391 : Type) ->
      (x_18392 : A_18391) ->
        (y_18393 : A_18391) ->
          (P_18394 : (A_18391) -> Linear) ->
            (e_18396 : (Eq_0 A_18391 x_18392 y_18393)) ->
              (f_18397 : (P_18394) x_18392) -> (P_18394) y_18393).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_18399 :=
  ((fix add_18400 m_18401 n_18402 =>
      match m_18401 with
      | (O_7 ) => n_18402
      | (S_8 m_18403) => (S_8 ((add_18400) m_18403) n_18402)
      end) :
    (m_18404 : Nat_6) -> (n_18405 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_18406 : Type) (F_18407 : (A_18406) -> Type) : Type :=
| pair_13 (A_18409 : Type)
            (F_18410 : (A_18409) -> Type)
              : (x_18412 : A_18409) ->
                  ((F_18410) x_18412) -> (Sigma_12 A_18409 F_18410).

Inductive Tensor_14 (A_18414 : Linear) (B_18415 : Linear) : Linear :=
| tpair_15 (A_18416 : Linear)
             (B_18417 : Linear)
               : (A_18416) -> (B_18417) -> (Tensor_14 A_18416 B_18417).

Inductive FTensor_16 (A_18420 : Type)
                       (F_18421 : (A_18420) -> Linear) : Linear :=
| fpair_17 (A_18423 : Type)
             (F_18424 : (A_18423) -> Linear)
               : (x_18426 : A_18423) ->
                   ((F_18424) x_18426) -> (FTensor_16 A_18423 F_18424).

Axiom unsafeC_18428 : (A_18429 : Linear) -> (A_18429) -> Unit_2.

Axiom unsafeP_18431 : (A_18432 : Linear) -> A_18432.

Definition Loc_18433 := ((Nat_6) : Type).

Axiom PtsTo_18434 : (Loc_18433) -> (Type) -> Linear.

Definition Ptr_18437 :=
  ((fun A_18438 =>
      (FTensor_16 Loc_18433 fun l_18439 => ((PtsTo_18434) l_18439) A_18438)) :
    (A_18440 : Type) -> Linear).

Axiom New_18441 : (A_18442 : Type) -> (A_18442) -> (Ptr_18437) A_18442.

Axiom Free_18444 : (A_18445 : Type) -> ((Ptr_18437) A_18445) -> Unit_2.

Axiom Get_18447 :
  (A_18448 : Type) ->
    (l_18449 : Loc_18433) ->
      (((PtsTo_18434) l_18449) A_18448) ->
        (FTensor_16 A_18448 fun __18451 => ((PtsTo_18434) l_18449) A_18448).

Axiom Set_18452 :
  (A_18453 : Type) ->
    (B_18454 : Type) ->
      (B_18454) ->
        (l_18456 : Loc_18433) ->
          (((PtsTo_18434) l_18456) A_18453) ->
            ((PtsTo_18434) l_18456) B_18454.

Inductive le_25 (n_18458 : Nat_6) : (Nat_6) -> Type :=
| le_n_26 (n_18460 : Nat_6) : (le_25 n_18460 n_18460)
| le_S_27 (n_18461 : Nat_6)
            : (m_18462 : Nat_6) ->
                ((le_25 n_18461 m_18462)) -> (le_25 n_18461 (S_8 m_18462)).

Definition lt_18464 :=
  ((fun m_18465 n_18466 => (le_25 (S_8 m_18465) n_18466)) :
    (m_18467 : Nat_6) -> (n_18468 : Nat_6) -> Type).

Inductive ArrVec_28 (A_18469 : Type)
                      (l_18470 : Loc_18433) : (Nat_6) -> Linear :=
| Nil_29 (A_18472 : Type)
           (l_18473 : Loc_18433) : (ArrVec_28 A_18472 l_18473 O_7)
| Cons_30 (A_18474 : Type)
            (l_18475 : Loc_18433)
              : (n_18476 : Nat_6) ->
                  (((PtsTo_18434) ((add_18399) l_18475) n_18476) A_18474) ->
                    ((ArrVec_28 A_18474 l_18475 n_18476)) ->
                      (ArrVec_28 A_18474 l_18475 (S_8 n_18476)).

Definition Array_18479 :=
  ((fun A_18480 n_18481 =>
      (FTensor_16
        Loc_18433 fun l_18482 => (ArrVec_28 A_18480 l_18482 n_18481))) :
    (A_18483 : Type) -> (n_18484 : Nat_6) -> Linear).

Definition nth_18485 :=
  ((fix nth_18486 A_18487 l_18488 m_18489 n_18490 pf_18491 v_18492 =>
      (match pf_18491 in (le_25 __18494 n_18495) return
         ((ArrVec_28 A_18487 l_18488 n_18495)) ->
           (Tensor_14
             ((PtsTo_18434) ((add_18399) l_18488) m_18489) A_18487
               (((PtsTo_18434) ((add_18399) l_18488) m_18489) A_18487) >>
                 (ArrVec_28 A_18487 l_18488 n_18495))
       with
       | (le_n_26 ) =>
         fun v_18498 =>
           (match v_18498 in (ArrVec_28 __18500 __18501 n_18502) return
              match n_18502 with
              | (O_7 ) => Base_4
              | (S_8 n0_18503) =>
                ((Eq_0 Nat_6 m_18489 n0_18503)) >>
                  (Tensor_14
                    ((PtsTo_18434) ((add_18399) l_18488) n0_18503) A_18487
                      (((PtsTo_18434) ((add_18399) l_18488) n0_18503) A_18487) >>
                        (ArrVec_28 A_18487 l_18488 n_18502))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_18506 c_18507 v_18508) =>
              fun __18509 =>
                (tpair_15 c_18507
                            fun c_18510 => (Cons_30 n_18506 c_18510 v_18508))
            end) refl_1
       | (le_S_27 __18511 pf_18512) =>
         fun v_18513 =>
           (match v_18513 in (ArrVec_28 __18515 __18516 n_18517) return
              match n_18517 with
              | (O_7 ) => Base_4
              | (S_8 n0_18518) =>
                (((lt_18464) m_18489) n0_18518) >>
                  (Tensor_14
                    ((PtsTo_18434) ((add_18399) l_18488) m_18489) A_18487
                      (((PtsTo_18434) ((add_18399) l_18488) m_18489) A_18487) >>
                        (ArrVec_28 A_18487 l_18488 n_18517))
              end
            with
            | (Nil_29 ) => ll_5
            | (Cons_30 n_18521 c0_18522 v0_18523) =>
              fun pf_18524 =>
                let x_18525 :=
                  ((((((nth_18486) A_18487) l_18488) m_18489) n_18521)
                     pf_18524)
                    v0_18523
                in
                match x_18525 with
                | (tpair_15 c_18526 f_18527) =>
                  (tpair_15 c_18526
                              fun c_18528 =>
                                (Cons_30 n_18521 c0_18522 (f_18527) c_18528))
                end
            end) pf_18512
       end) v_18492) :
    (A_18529 : Type) ->
      (l_18530 : Nat_6) ->
        (m_18531 : Nat_6) ->
          (n_18532 : Nat_6) ->
            (pf_18533 : ((lt_18464) m_18531) n_18532) ->
              (v_18534 : (ArrVec_28 A_18529 l_18530 n_18532)) ->
                (Tensor_14
                  ((PtsTo_18434) ((add_18399) l_18530) m_18531) A_18529
                    (((PtsTo_18434) ((add_18399) l_18530) m_18531) A_18529) >>
                      (ArrVec_28 A_18529 l_18530 n_18532))).

Definition index_18536 :=
  ((fun A_18537 m_18538 n_18539 pf_18540 a_18541 =>
      let x_18542 := a_18541 in
      match x_18542 with
      | (fpair_17 l_18543 v_18544) =>
        let x_18545 :=
          ((((((nth_18485) A_18537) l_18543) m_18538) n_18539) pf_18540)
            v_18544
        in
        match x_18545 with
        | (tpair_15 c_18546 f_18547) =>
          let x_18548 :=
            (((Get_18447) A_18537) ((add_18399) l_18543) m_18538) c_18546
          in
          match x_18548 with
          | (fpair_17 x_18549 c_18550) =>
            (fpair_17 x_18549 (fpair_17 l_18543 (f_18547) c_18550))
          end
        end
      end) :
    (A_18551 : Type) ->
      (m_18552 : Nat_6) ->
        (n_18553 : Nat_6) ->
          (pf_18554 : ((lt_18464) m_18552) n_18553) ->
            (a_18555 : ((Array_18479) A_18551) n_18553) ->
              (FTensor_16
                A_18551 fun __18556 => ((Array_18479) A_18551) n_18553)).

Definition Just0_18557 :=
  (((Sigma_12 Nat_6 fun x_18558 => (Eq_0 Nat_6 x_18558 O_7))) : Type).

Definition silly_18559 :=
  ((fun m_18560 n_18561 pf_18562 a_18563 =>
      let x_18564 :=
        (((((index_18536) Just0_18557) m_18560) n_18561) pf_18562) a_18563
      in
      match x_18564 with
      | (fpair_17 x_pf_18565 a_18566) =>
        let x_18567 :=
          (((((index_18536) Just0_18557) m_18560) n_18561) pf_18562) a_18566
        in
        match x_18567 with
        | (fpair_17 y_pf_18568 a_18569) =>
          let x_18570 := x_pf_18565 in
          match x_18570 with
          | (pair_13 x_18571 pf1_18572) =>
            let x0_18573 := y_pf_18568 in
            match x0_18573 with
            | (pair_13 y_18574 pf2_18575) =>
              let pf2_18576 :=
                ((((Eq_sym_18349) Nat_6) y_18574) O_7) pf2_18575
              in
              let pf_18577 :=
                ((((((((Eq_trans_18332) Nat_6) x_18571) O_7) y_18574)
                     pf1_18572)
                    pf2_18576) :
                  (Eq_0 Nat_6 x_18571 y_18574))
              in a_18569
            end
          end
        end
      end) :
    (m_18578 : Nat_6) ->
      (n_18579 : Nat_6) ->
        (pf_18580 : ((lt_18464) m_18578) n_18579) ->
          (a_18581 : ((Array_18479) Just0_18557) n_18579) ->
            ((Array_18479) Just0_18557) n_18579).

Definition main_18582 := ((tt_3) : Unit_2).



tt_3

