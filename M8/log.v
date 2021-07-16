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

Inductive LnEq_25 (A_71 : Linear) (x_72 : A_71) : (A_71) -> Type :=
| ln_refl_26 (A_71 : Linear) (x_72 : A_71) : (LnEq_25 A_71 x_72 x_72).

Definition LnEq_trans_73 :=
  ((fun A_74 x_75 y_76 z_77 e1_78 e2_79 =>
      match e2_79 in (LnEq_25 __0 __0 y_76) return (LnEq_25 A_74 x_75 y_76)
      with
      | (ln_refl_26 ) => e1_78
      end) :
    (A_74 : Linear) ->
      (x_75~ : A_74) ->
        (y_76~ : A_74) ->
          (z_77~ : A_74) ->
            (e1_78 : (LnEq_25 A_74 x_75 y_76)) ->
              (e2_79 : (LnEq_25 A_74 y_76 z_77)) -> (LnEq_25 A_74 x_75 z_77)).

Definition LnEq_sym_80 :=
  ((fun A_81 x_82 y_83 e_84 =>
      match e_84 in (LnEq_25 __0 __0 y_83) return (LnEq_25 A_81 y_83 x_82)
      with
      | (ln_refl_26 ) => ln_refl_26
      end) :
    (A_81 : Linear) ->
      (x_82~ : A_81) ->
        (y_83~ : A_81) ->
          (e_84 : (LnEq_25 A_81 x_82 y_83)) -> (LnEq_25 A_81 y_83 x_82)).

Inductive LnSigma_27 (A_85 : Linear) (F_86 : A_85 -> Type) : Type :=
| ln_pair_28 (A_85 : Linear)
               (F_86 : A_85 -> Type)
                 : (x_90~ : A_85) -> ((F_86) x_90) -> (LnSigma_27 A_85 F_86).



Inductive Eq_0 (A_175 : Type) (x_176 : A_175) : (A_175) -> Type :=
| refl_1 (A_178 : Type) (x_179 : A_178) : (Eq_0 A_178 x_179 x_179).

Definition Eq_trans_180 :=
  ((fun A_181 x_182 y_183 z_184 e1_185 e2_186 =>
      match e2_186 in (Eq_0 __188 __189 y_190) return
        (Eq_0 A_181 x_182 y_190)
      with
      | (refl_1 ) => e1_185
      end) :
    (A_191 : Type) ->
      (x_192 : A_191) ->
        (y_193 : A_191) ->
          (z_194 : A_191) ->
            (e1_195 : (Eq_0 A_191 x_192 y_193)) ->
              (e2_196 : (Eq_0 A_191 y_193 z_194)) -> (Eq_0 A_191 x_192 z_194)).

Definition Eq_sym_197 :=
  ((fun A_198 x_199 y_200 e_201 =>
      match e_201 in (Eq_0 __203 __204 y_205) return (Eq_0 A_198 y_205 x_199)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_206 : Type) ->
      (x_207 : A_206) ->
        (y_208 : A_206) ->
          (e_209 : (Eq_0 A_206 x_207 y_208)) -> (Eq_0 A_206 y_208 x_207)).

Definition TyInd_210 :=
  ((fun A_211 x_212 y_213 P_214 e_215 f_216 =>
      match e_215 in (Eq_0 __218 __219 y_220) return (P_214) y_220 with
      | (refl_1 ) => f_216
      end) :
    (A_221 : Type) ->
      (x_222 : A_221) ->
        (y_223 : A_221) ->
          (P_224 : A_221 -> Type) ->
            (e_226 : (Eq_0 A_221 x_222 y_223)) ->
              (f_227 : (P_224) x_222) -> (P_224) y_223).

Definition LnInd_228 :=
  ((fun A_229 x_230 y_231 P_232 e_233 f_234 =>
      match e_233 in (Eq_0 __236 __237 y_238) return (P_232) y_238 with
      | (refl_1 ) => f_234
      end) :
    (A_239 : Type) ->
      (x_240 : A_239) ->
        (y_241 : A_239) ->
          (P_242 : A_239 -> Linear) ->
            (e_244 : (Eq_0 A_239 x_240 y_241)) ->
              (f_245 : (P_242) x_240) -> (P_242) y_241).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_247 :=
  ((fix add_248 m_249 n_250 =>
      match m_249 with
      | (O_7 ) => n_250
      | (S_8 m_251) => (S_8 ((add_248) m_251) n_250)
      end) :
    (m_252 : Nat_6) -> (n_253 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_254 : Type) (F_255 : A_254 -> Type) : Type :=
| pair_13 (A_257 : Type)
            (F_258 : A_257 -> Type)
              : (x_260 : A_257) -> ((F_258) x_260) -> (Sigma_12 A_257 F_258).

Inductive Tensor_14 (A_262 : Linear) (B_263 : Linear) : Linear :=
| tpair_15 (A_264 : Linear)
             (B_265 : Linear) : (A_264) -> (B_265) -> (Tensor_14 A_264 B_265).

Inductive FTensor_16 (A_268 : Type) (F_269 : A_268 -> Linear) : Linear :=
| fpair_17 (A_271 : Type)
             (F_272 : A_271 -> Linear)
               : (x_274 : A_271) ->
                   ((F_272) x_274) -> (FTensor_16 A_271 F_272).

Axiom unsafeC_276 : (A_277 : Linear) -> A_277 -> Unit_2.

Axiom unsafeP_279 : (A_280 : Linear) -> A_280.

Definition Loc_281 := ((Nat_6) : Type).

Axiom PtsTo_282 : Loc_281 -> Type -> Linear.

Definition Ptr_285 :=
  ((fun A_286 => (FTensor_16 Loc_281 fun l_287 => ((PtsTo_282) l_287) A_286)) :
    (A_288 : Type) -> Linear).

Axiom New_289 : (A_290 : Type) -> A_290 -> (Ptr_285) A_290.

Axiom Free_292 : (A_293 : Type) -> (Ptr_285) A_293 -> Unit_2.

Axiom Get_295 :
  (A_296 : Type) ->
    (l_297 : Loc_281) ->
      ((PtsTo_282) l_297) A_296 ->
        (FTensor_16 A_296 fun __299 => ((PtsTo_282) l_297) A_296).

Axiom Set_300 :
  (A_301 : Type) ->
    (B_302 : Type) ->
      B_302 ->
        (l_304 : Loc_281) ->
          ((PtsTo_282) l_304) A_301 -> ((PtsTo_282) l_304) B_302.

Inductive LnEq_25 (A_306 : Linear) (x_307 : A_306) : (A_306) -> Type :=
| ln_refl_26 (A_309 : Linear) (x_310 : A_309) : (LnEq_25 A_309 x_310 x_310).

Definition LnEq_trans_311 :=
  ((fun A_312 x_313 y_314 z_315 e1_316 e2_317 =>
      match e2_317 in (LnEq_25 __319 __320 y_321) return
        (LnEq_25 A_312 x_313 y_321)
      with
      | (ln_refl_26 ) => e1_316
      end) :
    (A_322 : Linear) ->
      (x_323 : A_322) ->
        (y_324 : A_322) ->
          (z_325 : A_322) ->
            (e1_326 : (LnEq_25 A_322 x_323 y_324)) ->
              (e2_327 : (LnEq_25 A_322 y_324 z_325)) ->
                (LnEq_25 A_322 x_323 z_325)).

Definition LnEq_sym_328 :=
  ((fun A_329 x_330 y_331 e_332 =>
      match e_332 in (LnEq_25 __334 __335 y_336) return
        (LnEq_25 A_329 y_336 x_330)
      with
      | (ln_refl_26 ) => ln_refl_26
      end) :
    (A_337 : Linear) ->
      (x_338 : A_337) ->
        (y_339 : A_337) ->
          (e_340 : (LnEq_25 A_337 x_338 y_339)) ->
            (LnEq_25 A_337 y_339 x_338)).

Inductive LnSigma_27 (A_341 : Linear) (F_342 : A_341 -> Type) : Type :=
| ln_pair_28 (A_344 : Linear)
               (F_345 : A_344 -> Type)
                 : (x_347~ : A_344) ->
                     ((F_345) x_347) -> (LnSigma_27 A_344 F_345).



v_ctx  := {
  LnEq_sym :0
    ((A_773 : Linear) ->
       (x_774 : A_773) ->
         (y_775 : A_773) ->
           (e_776 : (LnEq_25 A_773 x_774 y_775)) ->
             (LnEq_25 A_773 y_775 x_774))::w
  LnEq_trans :0
    ((A_777 : Linear) ->
       (x_778 : A_777) ->
         (y_779 : A_777) ->
           (z_780 : A_777) ->
             (e1_781 : (LnEq_25 A_777 x_778 y_779)) ->
               (e2_782 : (LnEq_25 A_777 y_779 z_780)) ->
                 (LnEq_25 A_777 x_778 z_780))::w
  Set :0
    ((A_783 : Type) ->
       (B_784 : Type) ->
         B_784 ->
           (l_786 : ((Nat_6) : Type)) ->
             ((PtsTo_20) l_786) A_783 -> ((PtsTo_20) l_786) B_784)::w
  Get :0
    ((A_788 : Type) ->
       (l_789 : ((Nat_6) : Type)) ->
         ((PtsTo_20) l_789) A_788 ->
           (FTensor_16 A_788 fun __791 => ((PtsTo_20) l_789) A_788))::w
  Free :0
    ((A_792 : Type) ->
       (((fun A_794 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_795 => ((PtsTo_20) l_795) A_794)) :
          (A_796 : Type) -> Linear))
         A_792 -> Unit_2)::w
  New :0
    ((A_797 : Type) ->
       A_797 ->
         (((fun A_799 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_800 => ((PtsTo_20) l_800) A_799)) :
            (A_801 : Type) -> Linear))
           A_797)::w
  Ptr :0 ((A_802 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  unsafeP :0 ((A_805 : Linear) -> A_805)::w
  unsafeC :0 ((A_806 : Linear) -> A_806 -> Unit_2)::w
  add :0 ((m_808 : Nat_6) -> (n_809 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_810 : Type) ->
       (x_811 : A_810) ->
         (y_812 : A_810) ->
           (P_813 : A_810 -> Linear) ->
             (e_815 : (Eq_0 A_810 x_811 y_812)) ->
               (f_816 : (P_813) x_811) -> (P_813) y_812)::w
  TyInd :0
    ((A_817 : Type) ->
       (x_818 : A_817) ->
         (y_819 : A_817) ->
           (P_820 : A_817 -> Type) ->
             (e_822 : (Eq_0 A_817 x_818 y_819)) ->
               (f_823 : (P_820) x_818) -> (P_820) y_819)::w
  Eq_sym :0
    ((A_824 : Type) ->
       (x_825 : A_824) ->
         (y_826 : A_824) ->
           (e_827 : (Eq_0 A_824 x_825 y_826)) -> (Eq_0 A_824 y_826 x_825))::w
  Eq_trans :0
    ((A_828 : Type) ->
       (x_829 : A_828) ->
         (y_830 : A_828) ->
           (z_831 : A_828) ->
             (e1_832 : (Eq_0 A_828 x_829 y_830)) ->
               (e2_833 : (Eq_0 A_828 y_830 z_831)) ->
                 (Eq_0 A_828 x_829 z_831))::w
}

