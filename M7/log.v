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

Inductive Fin_23 : (Nat_6) -> Type :=
| F1_24 : (n_68 : Nat_6) -> (Fin_23 (S_8 n_68))
| FS_25 : (n_73 : Nat_6) -> ((Fin_23 n_73)) -> (Fin_23 (S_8 n_73)).

Inductive Vec_26 (A_75 : Type) : (Nat_6) -> Type :=
| Nil_27 (A_75 : Type) : (Vec_26 A_75 O_7)
| Cons_28 (A_75 : Type)
            : (n_79 : Nat_6) ->
                (A_75) -> ((Vec_26 A_75 n_79)) -> (Vec_26 A_75 (S_8 n_79)).

Definition nth_81 :=
  ((fix nth_81 A_82 n_83 x_84 v_85 =>
      (match x_84 in (Fin_23 n_83) return (Vec_26 A_82 n_83) -> A_82 with
       | (F1_24 n_83) =>
         fun v_85 =>
           match v_85 in (Vec_26 __0 n_83) return
             match n_83 with
             | (O_7 ) => Unit_2
             | (S_8 __0) => A_82
             end
           with
           | (Nil_27 ) => tt_3
           | (Cons_28 __0 x_84 __0) => x_84
           end
       | (FS_25 n_83 x_84) =>
         fun v_85 =>
           (match v_85 in (Vec_26 __0 n_83) return
              match n_83 with
              | (O_7 ) => Unit_2
              | (S_8 n_83) => (Fin_23 n_83) -> A_82
              end
            with
            | (Nil_27 ) => tt_3
            | (Cons_28 n_83 __0 v_85) =>
              fun x_84 => ((((nth_81) A_82) n_83) x_84) v_85
            end) x_84
       end) v_85) :
    (A_82 : Type) ->
      (n_83 : Nat_6) ->
        (x_84 : (Fin_23 n_83)) -> (v_85 : (Vec_26 A_82 n_83)) -> A_82).

Definition main_86 := ((tt_3) : Unit_2).



Inductive Eq_0 (A_173 : Type) (x_174 : A_173) : (A_173) -> Type :=
| refl_1 (A_176 : Type) (x_177 : A_176) : (Eq_0 A_176 x_177 x_177).

Definition Eq_trans_178 :=
  ((fun A_179 x_180 y_181 z_182 e1_183 e2_184 =>
      match e2_184 in (Eq_0 __186 __187 y_188) return
        (Eq_0 A_179 x_180 y_188)
      with
      | (refl_1 ) => e1_183
      end) :
    (A_189 : Type) ->
      (x_190 : A_189) ->
        (y_191 : A_189) ->
          (z_192 : A_189) ->
            (e1_193 : (Eq_0 A_189 x_190 y_191)) ->
              (e2_194 : (Eq_0 A_189 y_191 z_192)) -> (Eq_0 A_189 x_190 z_192)).

Definition Eq_sym_195 :=
  ((fun A_196 x_197 y_198 e_199 =>
      match e_199 in (Eq_0 __201 __202 y_203) return (Eq_0 A_196 y_203 x_197)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_204 : Type) ->
      (x_205 : A_204) ->
        (y_206 : A_204) ->
          (e_207 : (Eq_0 A_204 x_205 y_206)) -> (Eq_0 A_204 y_206 x_205)).

Definition TyInd_208 :=
  ((fun A_209 x_210 y_211 P_212 e_213 f_214 =>
      match e_213 in (Eq_0 __216 __217 y_218) return (P_212) y_218 with
      | (refl_1 ) => f_214
      end) :
    (A_219 : Type) ->
      (x_220 : A_219) ->
        (y_221 : A_219) ->
          (P_222 : A_219 -> Type) ->
            (e_224 : (Eq_0 A_219 x_220 y_221)) ->
              (f_225 : (P_222) x_220) -> (P_222) y_221).

Definition LnInd_226 :=
  ((fun A_227 x_228 y_229 P_230 e_231 f_232 =>
      match e_231 in (Eq_0 __234 __235 y_236) return (P_230) y_236 with
      | (refl_1 ) => f_232
      end) :
    (A_237 : Type) ->
      (x_238 : A_237) ->
        (y_239 : A_237) ->
          (P_240 : A_237 -> Linear) ->
            (e_242 : (Eq_0 A_237 x_238 y_239)) ->
              (f_243 : (P_240) x_238) -> (P_240) y_239).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_245 :=
  ((fix add_246 m_247 n_248 =>
      match m_247 with
      | (O_7 ) => n_248
      | (S_8 m_249) => (S_8 ((add_246) m_249) n_248)
      end) :
    (m_250 : Nat_6) -> (n_251 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_252 : Type) (F_253 : A_252 -> Type) : Type :=
| pair_13 (A_255 : Type)
            (F_256 : A_255 -> Type)
              : (x_258 : A_255) -> ((F_256) x_258) -> (Sigma_12 A_255 F_256).

Inductive Tensor_14 (A_260 : Linear) (B_261 : Linear) : Linear :=
| tpair_15 (A_262 : Linear)
             (B_263 : Linear) : (A_262) -> (B_263) -> (Tensor_14 A_262 B_263).

Inductive FTensor_16 (A_266 : Type) (F_267 : A_266 -> Linear) : Linear :=
| fpair_17 (A_269 : Type)
             (F_270 : A_269 -> Linear)
               : (x_272 : A_269) ->
                   ((F_270) x_272) -> (FTensor_16 A_269 F_270).

Definition Loc_274 := ((Nat_6) : Type).

Axiom PtsTo_275 : Loc_274 -> Type -> Linear.

Definition Ptr_278 :=
  ((fun A_279 => (FTensor_16 Loc_274 fun l_280 => ((PtsTo_275) l_280) A_279)) :
    (A_281 : Type) -> Linear).

Axiom New_282 : (A_283 : Type) -> A_283 -> (Ptr_278) A_283.

Axiom Free_285 : (A_286 : Type) -> (Ptr_278) A_286 -> Unit_2.

Axiom Get_288 :
  (A_289 : Type) ->
    (l_290 : Loc_274) ->
      ((PtsTo_275) l_290) A_289 ->
        (FTensor_16 A_289 fun __292 => ((PtsTo_275) l_290) A_289).

Axiom Set_293 :
  (A_294 : Type) ->
    (B_295 : Type) ->
      B_295 ->
        (l_297 : Loc_274) ->
          ((PtsTo_275) l_297) A_294 -> ((PtsTo_275) l_297) B_295.

Inductive Fin_23 : (Nat_6) -> Type :=
| F1_24 : (n_300 : Nat_6) -> (Fin_23 (S_8 n_300))
| FS_25 : (n_301 : Nat_6) -> ((Fin_23 n_301)) -> (Fin_23 (S_8 n_301)).

Inductive Vec_26 (A_303 : Type) : (Nat_6) -> Type :=
| Nil_27 (A_305 : Type) : (Vec_26 A_305 O_7)
| Cons_28 (A_306 : Type)
            : (n_307 : Nat_6) ->
                (A_306) ->
                  ((Vec_26 A_306 n_307)) -> (Vec_26 A_306 (S_8 n_307)).

Definition nth_310 :=
  ((fix nth_311 A_312 n_313 x_314 v_315 =>
      (match x_314 in (Fin_23 n_317) return (Vec_26 A_312 n_317) -> A_312
       with
       | (F1_24 n_319) =>
         fun v_320 =>
           match v_320 in (Vec_26 __322 n_323) return
             match n_323 with
             | (O_7 ) => Unit_2
             | (S_8 __324) => A_312
             end
           with
           | (Nil_27 ) => tt_3
           | (Cons_28 __325 x_326 __327) => x_326
           end
       | (FS_25 n_328 x_329) =>
         fun v_330 =>
           (match v_330 in (Vec_26 __332 n_333) return
              match n_333 with
              | (O_7 ) => Unit_2
              | (S_8 n_334) => (Fin_23 n_334) -> A_312
              end
            with
            | (Nil_27 ) => tt_3
            | (Cons_28 n_336 __337 v_338) =>
              fun x_339 => ((((nth_311) A_312) n_336) x_339) v_338
            end) x_329
       end) v_315) :
    (A_340 : Type) ->
      (n_341 : Nat_6) ->
        (x_342 : (Fin_23 n_341)) -> (v_343 : (Vec_26 A_340 n_341)) -> A_340).

Definition main_344 := ((tt_3) : Unit_2).



v_ctx  := {
  main :0 (Unit_2)::w
  nth :0
    ((A_1164 : Type) ->
       (n_1165 : Nat_6) ->
         (x_1166 : (Fin_23 n_1165)) ->
           (v_1167 : (Vec_26 A_1164 n_1165)) -> A_1164)::w
  Set :0
    ((A_1168 : Type) ->
       (B_1169 : Type) ->
         B_1169 ->
           (l_1171 : ((Nat_6) : Type)) ->
             ((PtsTo_18) l_1171) A_1168 -> ((PtsTo_18) l_1171) B_1169)::w
  Get :0
    ((A_1173 : Type) ->
       (l_1174 : ((Nat_6) : Type)) ->
         ((PtsTo_18) l_1174) A_1173 ->
           (FTensor_16 A_1173 fun __1176 => ((PtsTo_18) l_1174) A_1173))::w
  Free :0
    ((A_1177 : Type) ->
       (((fun A_1179 =>
            (FTensor_16
              ((Nat_6) : Type) fun l_1180 => ((PtsTo_18) l_1180) A_1179)) :
          (A_1181 : Type) -> Linear))
         A_1177 -> Unit_2)::w
  New :0
    ((A_1182 : Type) ->
       A_1182 ->
         (((fun A_1184 =>
              (FTensor_16
                ((Nat_6) : Type) fun l_1185 => ((PtsTo_18) l_1185) A_1184)) :
            (A_1186 : Type) -> Linear))
           A_1182)::w
  Ptr :0 ((A_1187 : Type) -> Linear)::w
  PtsTo :0 (((Nat_6) : Type) -> Type -> Linear)::w
  Loc :0 (Type)::w
  add :0 ((m_1190 : Nat_6) -> (n_1191 : Nat_6) -> Nat_6)::w
  LnInd :0
    ((A_1192 : Type) ->
       (x_1193 : A_1192) ->
         (y_1194 : A_1192) ->
           (P_1195 : A_1192 -> Linear) ->
             (e_1197 : (Eq_0 A_1192 x_1193 y_1194)) ->
               (f_1198 : (P_1195) x_1193) -> (P_1195) y_1194)::w
  TyInd :0
    ((A_1199 : Type) ->
       (x_1200 : A_1199) ->
         (y_1201 : A_1199) ->
           (P_1202 : A_1199 -> Type) ->
             (e_1204 : (Eq_0 A_1199 x_1200 y_1201)) ->
               (f_1205 : (P_1202) x_1200) -> (P_1202) y_1201)::w
  Eq_sym :0
    ((A_1206 : Type) ->
       (x_1207 : A_1206) ->
         (y_1208 : A_1206) ->
           (e_1209 : (Eq_0 A_1206 x_1207 y_1208)) ->
             (Eq_0 A_1206 y_1208 x_1207))::w
  Eq_trans :0
    ((A_1210 : Type) ->
       (x_1211 : A_1210) ->
         (y_1212 : A_1210) ->
           (z_1213 : A_1210) ->
             (e1_1214 : (Eq_0 A_1210 x_1211 y_1212)) ->
               (e2_1215 : (Eq_0 A_1210 y_1212 z_1213)) ->
                 (Eq_0 A_1210 x_1211 z_1213))::w
}

tt_3

