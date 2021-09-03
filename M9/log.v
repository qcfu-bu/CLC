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

Axiom new_76 : (A_80 : Type) -> (x_84 : A_80) -> (((ptsto_71) ?0) O_7) x_84.

Definition main_85 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_140 : Type) (x_141 : A_140) : (A_140) -> Type :=
| refl_1 (A_143 : Type) (x_144 : A_143) : (Eq_0 A_143 x_144 x_144).

Definition Eq_trans_145 :=
  ((fun A_146 x_147 y_148 z_149 e1_150 e2_151 =>
      match e2_151 in (Eq_0 __153 __154 y_155) return
        (Eq_0 A_146 x_147 y_155)
      with
      | (refl_1 ) => e1_150
      end) :
    (A_156 : Type) ->
      (x_157 : A_156) ->
        (y_158 : A_156) ->
          (z_159 : A_156) ->
            (e1_160 : (Eq_0 A_156 x_157 y_158)) ->
              (e2_161 : (Eq_0 A_156 y_158 z_159)) -> (Eq_0 A_156 x_157 z_159)).

Definition Eq_sym_162 :=
  ((fun A_163 x_164 y_165 e_166 =>
      match e_166 in (Eq_0 __168 __169 y_170) return (Eq_0 A_163 y_170 x_164)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_171 : Type) ->
      (x_172 : A_171) ->
        (y_173 : A_171) ->
          (e_174 : (Eq_0 A_171 x_172 y_173)) -> (Eq_0 A_171 y_173 x_172)).

Definition TyInd_175 :=
  ((fun A_176 x_177 y_178 P_179 e_180 f_181 =>
      match e_180 in (Eq_0 __183 __184 y_185) return (P_179) y_185 with
      | (refl_1 ) => f_181
      end) :
    (A_186 : Type) ->
      (x_187 : A_186) ->
        (y_188 : A_186) ->
          (P_189 : A_186 -> Type) ->
            (e_191 : (Eq_0 A_186 x_187 y_188)) ->
              (f_192 : (P_189) x_187) -> (P_189) y_188).

Definition LnInd_193 :=
  ((fun A_194 x_195 y_196 P_197 e_198 f_199 =>
      match e_198 in (Eq_0 __201 __202 y_203) return (P_197) y_203 with
      | (refl_1 ) => f_199
      end) :
    (A_204 : Type) ->
      (x_205 : A_204) ->
        (y_206 : A_204) ->
          (P_207 : A_204 -> Linear) ->
            (e_209 : (Eq_0 A_204 x_205 y_206)) ->
              (f_210 : (P_207) x_205) -> (P_207) y_206).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_212 :=
  ((fix add_213 m_214 n_215 =>
      match m_214 with
      | (O_7 ) => n_215
      | (S_8 m_216) => (S_8 ((add_213) m_216) n_215)
      end) :
    (m_217 : Nat_6) -> (n_218 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_219 : Type) (F_220 : A_219 -> Type) : Type :=
| pair_13 (A_222 : Type)
            (F_223 : A_222 -> Type)
              : (x_225 : A_222) -> ((F_223) x_225) -> (Sigma_12 A_222 F_223).

Inductive Tensor_14 (A_227 : Linear) (B_228 : Linear) : Linear :=
| tpair_15 (A_229 : Linear)
             (B_230 : Linear) : (A_229) -> (B_230) -> (Tensor_14 A_229 B_230).

Inductive FTensor_16 (A_233 : Type) (F_234 : A_233 -> Linear) : Linear :=
| fpair_17 (A_236 : Type)
             (F_237 : A_236 -> Linear)
               : (x_239 : A_236) ->
                   ((F_237) x_239) -> (FTensor_16 A_236 F_237).

Axiom unsafeC_241 : (A_242 : Linear) -> A_242 -> Unit_2.

Axiom unsafeP_244 : (A_245 : Linear) -> A_245.

Definition Loc_246 := ((Nat_6) : Type).

Axiom PtsTo_247 : Loc_246 -> Type -> Linear.

Definition Ptr_250 :=
  ((fun A_251 => (FTensor_16 Loc_246 fun l_252 => ((PtsTo_247) l_252) A_251)) :
    (A_253 : Type) -> Linear).

Axiom New_254 : (A_255 : Type) -> A_255 -> (Ptr_250) A_255.

Axiom Free_257 : (A_258 : Type) -> (Ptr_250) A_258 -> Unit_2.

Axiom Get_260 :
  (A_261 : Type) ->
    (l_262 : Loc_246) ->
      ((PtsTo_247) l_262) A_261 ->
        (FTensor_16 A_261 fun __264 => ((PtsTo_247) l_262) A_261).

Axiom Set_265 :
  (A_266 : Type) ->
    (B_267 : Type) ->
      B_267 ->
        (l_269 : Loc_246) ->
          ((PtsTo_247) l_269) A_266 -> ((PtsTo_247) l_269) B_267.

Axiom ptsto_271 : (A_272 : Type) -> Nat_6 -> A_272 -> Linear.

Axiom new_275 :
  (A_276 : Type) -> (x_277 : A_276) -> (((ptsto_271) ?0) O_7) x_277.

Definition main_278 := ((tt_3) : Unit_2).



TyProd A_337 (x_338 : A_337) ->
               (y_339 : A_337) ->
                 (z_340 : A_337) ->
                   (e1_341 : (Eq_0 A_337 x_338 y_339)) ->
                     (e2_342 : (Eq_0 A_337 y_339 z_340)) ->
                       (Eq_0 A_337 x_338 z_340)
TyProd x_343 (y_344 : A_337) ->
               (z_345 : A_337) ->
                 (e1_346 : (Eq_0 A_337 x_343 y_344)) ->
                   (e2_347 : (Eq_0 A_337 y_344 z_345)) ->
                     (Eq_0 A_337 x_343 z_345)
TyProd y_348 (z_349 : A_337) ->
               (e1_350 : (Eq_0 A_337 x_343 y_348)) ->
                 (e2_351 : (Eq_0 A_337 y_348 z_349)) ->
                   (Eq_0 A_337 x_343 z_349)
TyProd z_352 (e1_353 : (Eq_0 A_337 x_343 y_348)) ->
               (e2_354 : (Eq_0 A_337 y_348 z_352)) ->
                 (Eq_0 A_337 x_343 z_352)
TyProd e1_355 (e2_356 : (Eq_0 A_337 y_348 z_352)) -> (Eq_0 A_337 x_343 z_352)
TyProd e2_357 (Eq_0 A_337 x_343 z_352)
TyProd A_389 (x_390 : A_389) ->
               (y_391 : A_389) ->
                 (e_392 : (Eq_0 A_389 x_390 y_391)) ->
                   (Eq_0 A_389 y_391 x_390)
TyProd x_393 (y_394 : A_389) ->
               (e_395 : (Eq_0 A_389 x_393 y_394)) -> (Eq_0 A_389 y_394 x_393)
TyProd y_396 (e_397 : (Eq_0 A_389 x_393 y_396)) -> (Eq_0 A_389 y_396 x_393)
TyProd e_398 (Eq_0 A_389 y_396 x_393)
TyProd __404 Type
TyProd A_453 (x_454 : A_453) ->
               (y_455 : A_453) ->
                 (P_456 : A_453 -> Type) ->
                   (e_458 : (Eq_0 A_453 x_454 y_455)) ->
                     (f_459 : (P_456) x_454) -> (P_456) y_455
TyProd x_460 (y_461 : A_453) ->
               (P_462 : A_453 -> Type) ->
                 (e_464 : (Eq_0 A_453 x_460 y_461)) ->
                   (f_465 : (P_462) x_460) -> (P_462) y_461
TyProd y_466 (P_467 : A_453 -> Type) ->
               (e_469 : (Eq_0 A_453 x_460 y_466)) ->
                 (f_470 : (P_467) x_460) -> (P_467) y_466
TyProd P_471 (e_472 : (Eq_0 A_453 x_460 y_466)) ->
               (f_473 : (P_471) x_460) -> (P_471) y_466
TyProd __474 Type
TyProd e_475 (f_476 : (P_471) x_460) -> (P_471) y_466
TyProd f_477 (P_471) y_466
TyProd __483 Linear
TyProd A_532 (x_533 : A_532) ->
               (y_534 : A_532) ->
                 (P_535 : A_532 -> Linear) ->
                   (e_537 : (Eq_0 A_532 x_533 y_534)) ->
                     (f_538 : (P_535) x_533) -> (P_535) y_534
TyProd x_539 (y_540 : A_532) ->
               (P_541 : A_532 -> Linear) ->
                 (e_543 : (Eq_0 A_532 x_539 y_540)) ->
                   (f_544 : (P_541) x_539) -> (P_541) y_540
TyProd y_545 (P_546 : A_532 -> Linear) ->
               (e_548 : (Eq_0 A_532 x_539 y_545)) ->
                 (f_549 : (P_546) x_539) -> (P_546) y_545
TyProd P_550 (e_551 : (Eq_0 A_532 x_539 y_545)) ->
               (f_552 : (P_550) x_539) -> (P_550) y_545
TyProd __553 Linear
TyProd e_554 (f_555 : (P_550) x_539) -> (P_550) y_545
TyProd f_556 (P_550) y_545
TyProd m_561 (n_562 : Nat_6) -> Nat_6
TyProd n_563 Nat_6
TyProd m_572 (n_573 : Nat_6) -> Nat_6
TyProd n_574 Nat_6
TyProd __578 Type
TyProd __581 Type
TyProd __605 Linear
TyProd __608 Linear
TyProd A_620 A_620 -> Unit_2
TyProd __622 Unit_2
TyProd A_623 A_623 -> Unit_2
TyProd __625 Unit_2
TyProd A_627 A_627
TyProd A_628 A_628
TyProd __631 Type -> Linear
TyProd __633 Linear
TyProd __634 Type -> Linear
TyProd __636 Linear
TyProd __640 Type -> Linear
TyProd __642 Linear
TyProd A_646 Linear
TyProd A_648 A_648 ->
               (((fun A_650 =>
                    (FTensor_16
                      ((Nat_6) : Type) fun l_651 => ((PtsTo_20) l_651) A_650)) :
                  (A_652 : Type) -> Linear))
                 A_648
TyProd __653 (((fun A_654 =>
                  (FTensor_16
                    ((Nat_6) : Type) fun l_655 => ((PtsTo_20) l_655) A_654)) :
                (A_656 : Type) -> Linear))
               A_648
TyProd __659 Type -> Linear
TyProd __661 Linear
TyProd A_665 A_665 ->
               (((fun A_667 =>
                    (FTensor_16
                      ((Nat_6) : Type) fun l_668 => ((PtsTo_20) l_668) A_667)) :
                  (A_669 : Type) -> Linear))
                 A_665
TyProd __670 (((fun A_671 =>
                  (FTensor_16
                    ((Nat_6) : Type) fun l_672 => ((PtsTo_20) l_672) A_671)) :
                (A_673 : Type) -> Linear))
               A_665
TyProd __676 Type -> Linear
TyProd __678 Linear
TyProd A_683 (((fun A_685 =>
                  (FTensor_16
                    ((Nat_6) : Type) fun l_686 => ((PtsTo_20) l_686) A_685)) :
                (A_687 : Type) -> Linear))
               A_683 -> Unit_2
TyProd __688 Unit_2
TyProd __691 Type -> Linear
TyProd __693 Linear
TyProd A_697 (((fun A_699 =>
                  (FTensor_16
                    ((Nat_6) : Type) fun l_700 => ((PtsTo_20) l_700) A_699)) :
                (A_701 : Type) -> Linear))
               A_697 -> Unit_2
TyProd __702 Unit_2
TyProd __705 Type -> Linear
TyProd __707 Linear
TyProd A_712 (l_713 : ((Nat_6) : Type)) ->
               ((PtsTo_20) l_713) A_712 ->
                 (FTensor_16 A_712 fun __715 => ((PtsTo_20) l_713) A_712)
TyProd l_716 ((PtsTo_20) l_716) A_712 ->
               (FTensor_16 A_712 fun __718 => ((PtsTo_20) l_716) A_712)
TyProd __719 (FTensor_16 A_712 fun __720 => ((PtsTo_20) l_716) A_712)
TyProd __721 Type -> Linear
TyProd __723 Linear
TyProd __725 Type -> Linear
TyProd __727 Linear
TyProd A_729 (l_730 : ((Nat_6) : Type)) ->
               ((PtsTo_20) l_730) A_729 ->
                 (FTensor_16 A_729 fun __732 => ((PtsTo_20) l_730) A_729)
TyProd l_733 ((PtsTo_20) l_733) A_729 ->
               (FTensor_16 A_729 fun __735 => ((PtsTo_20) l_733) A_729)
TyProd __736 (FTensor_16 A_729 fun __737 => ((PtsTo_20) l_733) A_729)
TyProd __738 Type -> Linear
TyProd __740 Linear
TyProd __742 Type -> Linear
TyProd __744 Linear
TyProd A_747 (B_748 : Type) ->
               B_748 ->
                 (l_750 : ((Nat_6) : Type)) ->
                   ((PtsTo_20) l_750) A_747 -> ((PtsTo_20) l_750) B_748
TyProd B_752 B_752 ->
               (l_754 : ((Nat_6) : Type)) ->
                 ((PtsTo_20) l_754) A_747 -> ((PtsTo_20) l_754) B_752
TyProd __756 (l_757 : ((Nat_6) : Type)) ->
               ((PtsTo_20) l_757) A_747 -> ((PtsTo_20) l_757) B_752
TyProd l_759 ((PtsTo_20) l_759) A_747 -> ((PtsTo_20) l_759) B_752
TyProd __761 ((PtsTo_20) l_759) B_752
TyProd __762 Type -> Linear
TyProd __764 Linear
TyProd __765 Type -> Linear
TyProd __767 Linear
TyProd A_768 (B_769 : Type) ->
               B_769 ->
                 (l_771 : ((Nat_6) : Type)) ->
                   ((PtsTo_20) l_771) A_768 -> ((PtsTo_20) l_771) B_769
TyProd B_773 B_773 ->
               (l_775 : ((Nat_6) : Type)) ->
                 ((PtsTo_20) l_775) A_768 -> ((PtsTo_20) l_775) B_773
TyProd __777 (l_778 : ((Nat_6) : Type)) ->
               ((PtsTo_20) l_778) A_768 -> ((PtsTo_20) l_778) B_773
TyProd l_780 ((PtsTo_20) l_780) A_768 -> ((PtsTo_20) l_780) B_773
TyProd __782 ((PtsTo_20) l_780) B_773
TyProd __783 Type -> Linear
TyProd __785 Linear
TyProd __786 Type -> Linear
TyProd __788 Linear
TyProd A_790 Nat_6 -> A_790 -> Linear
TyProd __793 A_790 -> Linear
TyProd __795 Linear
TyProd A_796 Nat_6 -> A_796 -> Linear
TyProd __799 A_796 -> Linear
TyProd __801 Linear
TyProd A_803 (x_804 : A_803) -> (((ptsto_25) ?0) O_7) x_804
TyProd x_805 (((ptsto_25) ?0) O_7) x_805
TyProd A_806 Nat_6 -> A_806 -> Linear
TyProd __809 A_806 -> Linear
TyProd __811 Linear
TyProd A_812 (x_813 : A_812) -> (((ptsto_25) A_803) O_7) x_813
TyProd x_814 (((ptsto_25) A_803) O_7) x_814
TyProd A_815 Nat_6 -> A_815 -> Linear
TyProd __818 A_815 -> Linear
TyProd __820 Linear
{
  x_814 :Type (A_812)
  A_812 :Type (Type)
  ptsto_802 :Type ((A_821 : Type) -> Nat_6 -> A_821 -> Linear)
  Set_789 :Type
    ((A_824 : Type) ->
       (B_825 : Type) ->
         B_825 ->
           (l_827 : ((Nat_6) : Type)) ->
             ((PtsTo_20) l_827) A_824 -> ((PtsTo_20) l_827) B_825)
  Get_746 :Type
    ((A_829 : Type) ->
       (l_830 : ((Nat_6) : Type)) ->
         ((PtsTo_20) l_830) A_829 ->
           (FTensor_16 A_829 fun __832 => ((PtsTo_20) l_830) A_829))
  Free_711 :Type
    ((A_833 : Type) ->
       (((fun A_835 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_836 => ((PtsTo_20) l_836) A_835)) :
          (A_837 : Type) -> Linear))
         A_833 -> Unit_2)
  New_682 :Type
    ((A_838 : Type) ->
       A_838 ->
         (((fun A_840 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_841 => ((PtsTo_20) l_841) A_840)) :
            (A_842 : Type) -> Linear))
           A_838)
  Ptr_647 :Type ((A_843 : Type) -> Linear)
  PtsTo_637 :Type (((Nat_6) : Type) -> Type -> Linear)
  Loc_630 :Type (Type)
  unsafeP_629 :Type ((A_846 : Linear) -> A_846)
  unsafeC_626 :Type ((A_847 : Linear) -> A_847 -> Unit_2)
  add_575 :Type ((m_849 : Nat_6) -> (n_850 : Nat_6) -> Nat_6)
  LnInd_557 :Type
    ((A_851 : Type) ->
       (x_852 : A_851) ->
         (y_853 : A_851) ->
           (P_854 : A_851 -> Linear) ->
             (e_856 : (Eq_0 A_851 x_852 y_853)) ->
               (f_857 : (P_854) x_852) -> (P_854) y_853)
  TyInd_478 :Type
    ((A_858 : Type) ->
       (x_859 : A_858) ->
         (y_860 : A_858) ->
           (P_861 : A_858 -> Type) ->
             (e_863 : (Eq_0 A_858 x_859 y_860)) ->
               (f_864 : (P_861) x_859) -> (P_861) y_860)
  Eq_sym_399 :Type
    ((A_865 : Type) ->
       (x_866 : A_865) ->
         (y_867 : A_865) ->
           (e_868 : (Eq_0 A_865 x_866 y_867)) -> (Eq_0 A_865 y_867 x_866))
  Eq_trans_358 :Type
    ((A_869 : Type) ->
       (x_870 : A_869) ->
         (y_871 : A_869) ->
           (z_872 : A_869) ->
             (e1_873 : (Eq_0 A_869 x_870 y_871)) ->
               (e2_874 : (Eq_0 A_869 y_871 z_872)) ->
                 (Eq_0 A_869 x_870 z_872))
}