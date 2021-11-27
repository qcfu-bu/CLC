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

Definition LnEq_trans_73~ :=
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

Inductive LnSigma_27 (A_85 : Linear) (F_86 : A_85 -> Type) : Linear :=
| ln_pair_28 (A_85 : Linear)
               (F_86 : A_85 -> Type)
                 : (x_90 : A_85) -> ((F_86) x_90) -> (LnSigma_27 A_85 F_86).

Axiom get_91 :
  (A_95 : Type) ->
    (l_99 : Loc_48) ->
      (c_103 : ((PtsTo_49) l_99) A_95) ->
        (FTensor_16
          A_95
            fun __0 =>
              (LnSigma_27
                ((PtsTo_49) l_99) A_95
                  fun c'_107 => (LnEq_25 ((PtsTo_49) l_99) A_95 c_103 c'_107))).



Inductive Eq_0 (A_181 : Type) (x_182 : A_181) : (A_181) -> Type :=
| refl_1 (A_184 : Type) (x_185 : A_184) : (Eq_0 A_184 x_185 x_185).

Definition Eq_trans_186 :=
  ((fun A_187 x_188 y_189 z_190 e1_191 e2_192 =>
      match e2_192 in (Eq_0 __194 __195 y_196) return
        (Eq_0 A_187 x_188 y_196)
      with
      | (refl_1 ) => e1_191
      end) :
    (A_197 : Type) ->
      (x_198 : A_197) ->
        (y_199 : A_197) ->
          (z_200 : A_197) ->
            (e1_201 : (Eq_0 A_197 x_198 y_199)) ->
              (e2_202 : (Eq_0 A_197 y_199 z_200)) -> (Eq_0 A_197 x_198 z_200)).

Definition Eq_sym_203 :=
  ((fun A_204 x_205 y_206 e_207 =>
      match e_207 in (Eq_0 __209 __210 y_211) return (Eq_0 A_204 y_211 x_205)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_212 : Type) ->
      (x_213 : A_212) ->
        (y_214 : A_212) ->
          (e_215 : (Eq_0 A_212 x_213 y_214)) -> (Eq_0 A_212 y_214 x_213)).

Definition TyInd_216 :=
  ((fun A_217 x_218 y_219 P_220 e_221 f_222 =>
      match e_221 in (Eq_0 __224 __225 y_226) return (P_220) y_226 with
      | (refl_1 ) => f_222
      end) :
    (A_227 : Type) ->
      (x_228 : A_227) ->
        (y_229 : A_227) ->
          (P_230 : A_227 -> Type) ->
            (e_232 : (Eq_0 A_227 x_228 y_229)) ->
              (f_233 : (P_230) x_228) -> (P_230) y_229).

Definition LnInd_234 :=
  ((fun A_235 x_236 y_237 P_238 e_239 f_240 =>
      match e_239 in (Eq_0 __242 __243 y_244) return (P_238) y_244 with
      | (refl_1 ) => f_240
      end) :
    (A_245 : Type) ->
      (x_246 : A_245) ->
        (y_247 : A_245) ->
          (P_248 : A_245 -> Linear) ->
            (e_250 : (Eq_0 A_245 x_246 y_247)) ->
              (f_251 : (P_248) x_246) -> (P_248) y_247).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_253 :=
  ((fix add_254 m_255 n_256 =>
      match m_255 with
      | (O_7 ) => n_256
      | (S_8 m_257) => (S_8 ((add_254) m_257) n_256)
      end) :
    (m_258 : Nat_6) -> (n_259 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_260 : Type) (F_261 : A_260 -> Type) : Type :=
| pair_13 (A_263 : Type)
            (F_264 : A_263 -> Type)
              : (x_266 : A_263) -> ((F_264) x_266) -> (Sigma_12 A_263 F_264).

Inductive Tensor_14 (A_268 : Linear) (B_269 : Linear) : Linear :=
| tpair_15 (A_270 : Linear)
             (B_271 : Linear) : (A_270) -> (B_271) -> (Tensor_14 A_270 B_271).

Inductive FTensor_16 (A_274 : Type) (F_275 : A_274 -> Linear) : Linear :=
| fpair_17 (A_277 : Type)
             (F_278 : A_277 -> Linear)
               : (x_280 : A_277) ->
                   ((F_278) x_280) -> (FTensor_16 A_277 F_278).

Axiom unsafeC_282 : (A_283 : Linear) -> A_283 -> Unit_2.

Axiom unsafeP_285 : (A_286 : Linear) -> A_286.

Definition Loc_287 := ((Nat_6) : Type).

Axiom PtsTo_288 : Loc_287 -> Type -> Linear.

Definition Ptr_291 :=
  ((fun A_292 => (FTensor_16 Loc_287 fun l_293 => ((PtsTo_288) l_293) A_292)) :
    (A_294 : Type) -> Linear).

Axiom New_295 : (A_296 : Type) -> A_296 -> (Ptr_291) A_296.

Axiom Free_298 : (A_299 : Type) -> (Ptr_291) A_299 -> Unit_2.

Axiom Get_301 :
  (A_302 : Type) ->
    (l_303 : Loc_287) ->
      ((PtsTo_288) l_303) A_302 ->
        (FTensor_16 A_302 fun __305 => ((PtsTo_288) l_303) A_302).

Axiom Set_306 :
  (A_307 : Type) ->
    (B_308 : Type) ->
      B_308 ->
        (l_310 : Loc_287) ->
          ((PtsTo_288) l_310) A_307 -> ((PtsTo_288) l_310) B_308.

Inductive LnEq_25 (A_312 : Linear) (x_313 : A_312) : (A_312) -> Type :=
| ln_refl_26 (A_315 : Linear) (x_316 : A_315) : (LnEq_25 A_315 x_316 x_316).

Definition LnEq_trans_317~ :=
  ((fun A_318 x_319 y_320 z_321 e1_322 e2_323 =>
      match e2_323 in (LnEq_25 __325 __326 y_327) return
        (LnEq_25 A_318 x_319 y_327)
      with
      | (ln_refl_26 ) => e1_322
      end) :
    (A_328 : Linear) ->
      (x_329 : A_328) ->
        (y_330 : A_328) ->
          (z_331 : A_328) ->
            (e1_332 : (LnEq_25 A_328 x_329 y_330)) ->
              (e2_333 : (LnEq_25 A_328 y_330 z_331)) ->
                (LnEq_25 A_328 x_329 z_331)).

Definition LnEq_sym_334 :=
  ((fun A_335 x_336 y_337 e_338 =>
      match e_338 in (LnEq_25 __340 __341 y_342) return
        (LnEq_25 A_335 y_342 x_336)
      with
      | (ln_refl_26 ) => ln_refl_26
      end) :
    (A_343 : Linear) ->
      (x_344 : A_343) ->
        (y_345 : A_343) ->
          (e_346 : (LnEq_25 A_343 x_344 y_345)) ->
            (LnEq_25 A_343 y_345 x_344)).

Inductive LnSigma_27 (A_347 : Linear) (F_348 : A_347~ -> Type) : Linear :=
| ln_pair_28 (A_350 : Linear)
               (F_351 : A_350~ -> Type)
                 : (x_353 : A_350) ->
                     ((F_351) x_353) -> (LnSigma_27 A_350 F_351).

Axiom get_355 :
  (A_356 : Type) ->
    (l_357 : Loc_287) ->
      (c_358 : ((PtsTo_288) l_357) A_356) ->
        (FTensor_16
          A_356
            fun __359 =>
              (LnSigma_27
                ((PtsTo_288) l_357) A_356
                  fun c'_360 =>
                    (LnEq_25 ((PtsTo_288) l_357) A_356 c_358 c'_360))).



v_ctx  := {
  get :0
    ((A_844 : Type) ->
       (l_845 : ((Nat_6) : Type)) ->
         (c_846 : ((PtsTo_20) l_845) A_844) ->
           (FTensor_16
             A_844
               fun __847 =>
                 (LnSigma_27
                   ((PtsTo_20) l_845) A_844
                     fun c'_848 =>
                       (LnEq_25 ((PtsTo_20) l_845) A_844 c_846 c'_848))))::w
  LnEq_sym :0
    ((A_849 : Linear) ->
       (x_850 : A_849) ->
         (y_851 : A_849) ->
           (e_852 : (LnEq_25 A_849 x_850 y_851)) ->
             (LnEq_25 A_849 y_851 x_850))::w
  LnEq_trans :0
    ((A_853 : Linear) ->
       (x_854 : A_853) ->
         (y_855 : A_853) ->
           (z_856 : A_853) ->
             (e1_857 : (LnEq_25 A_853 x_854 y_855)) ->
               (e2_858 : (LnEq_25 A_853 y_855 z_856)) ->
                 (LnEq_25 A_853 x_854 z_856))::w
  Set :0
    ((A_859 : Type) ->
       (B_860 : Type) ->
         B_860 ->
           (l_862 : ((Nat_6) : Type)) ->
             ((PtsTo_20) l_862) A_859 -> ((PtsTo_20) l_862) B_860)::w
  Get :0
    ((A_864 : Type) ->
       (l_865 : ((Nat_6) : Type)) ->
         ((PtsTo_20) l_865) A_864 ->
           (FTensor_16 A_864 fun __867 => ((PtsTo_20) l_865) A_864))::w
  Free :0
    ((A_868 : Type) ->
       (((fun A_870 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_871 => ((PtsTo_20) l_871) A_870)) :
          (A_872 : Type) -> Linear))
         A_868 -> Unit_2)::w
  New :0
    ((A_873 : Type) ->
       A_873 ->
         (((fun A_875 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_876 => ((PtsTo_20) l_876) A_875)) :
            (A_877 : Type) -> Linear))
           A_873)::w
  Ptr :0 ((A_878 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  unsafeP :0 ((A_881 : Linear) -> A_881)::w
  unsafeC :0 ((A_882 : Linear) -> A_882 -> Unit_2)::w
  add :0 ((m_884 : Nat_6) -> (n_885 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_886 : Type) ->
       (x_887 : A_886) ->
         (y_888 : A_886) ->
           (P_889 : A_886 -> Linear) ->
             (e_891 : (Eq_0 A_886 x_887 y_888)) ->
               (f_892 : (P_889) x_887) -> (P_889) y_888)::w
  TyInd :0
    ((A_893 : Type) ->
       (x_894 : A_893) ->
         (y_895 : A_893) ->
           (P_896 : A_893 -> Type) ->
             (e_898 : (Eq_0 A_893 x_894 y_895)) ->
               (f_899 : (P_896) x_894) -> (P_896) y_895)::w
  Eq_sym :0
    ((A_900 : Type) ->
       (x_901 : A_900) ->
         (y_902 : A_900) ->
           (e_903 : (Eq_0 A_900 x_901 y_902)) -> (Eq_0 A_900 y_902 x_901))::w
  Eq_trans :0
    ((A_904 : Type) ->
       (x_905 : A_904) ->
         (y_906 : A_904) ->
           (z_907 : A_904) ->
             (e1_908 : (Eq_0 A_904 x_905 y_906)) ->
               (e2_909 : (Eq_0 A_904 y_906 z_907)) ->
                 (Eq_0 A_904 x_905 z_907))::w
}

