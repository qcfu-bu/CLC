parse ok
desugar ok
elab ok
resolve ok
tcheck ok
Inductive Eq_0 (A_19262 : Type) (x_19263 : A_19262) : (A_19262) -> Type :=
| refl_1 (A_19265 : Type)
           (x_19266 : A_19265) : (Eq_0 A_19265 x_19266 x_19266).

Definition Eq_trans_19267 :=
  ((fun A_19268 x_19269 y_19270 z_19271 e1_19272 e2_19273 =>
      match e2_19273 in (Eq_0 __19275 __19276 y_19277) return
        (Eq_0 A_19268 x_19269 y_19277)
      with
      | (refl_1 ) => e1_19272
      end) :
    (A_19278 : Type) ->
      (x_19279 : A_19278) ->
        (y_19280 : A_19278) ->
          (z_19281 : A_19278) ->
            (e1_19282 : (Eq_0 A_19278 x_19279 y_19280)) ->
              (e2_19283 : (Eq_0 A_19278 y_19280 z_19281)) ->
                (Eq_0 A_19278 x_19279 z_19281)).

Definition Eq_sym_19284 :=
  ((fun A_19285 x_19286 y_19287 e_19288 =>
      match e_19288 in (Eq_0 __19290 __19291 y_19292) return
        (Eq_0 A_19285 y_19292 x_19286)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_19293 : Type) ->
      (x_19294 : A_19293) ->
        (y_19295 : A_19293) ->
          (e_19296 : (Eq_0 A_19293 x_19294 y_19295)) ->
            (Eq_0 A_19293 y_19295 x_19294)).

Definition TyInd_19297 :=
  ((fun A_19298 x_19299 y_19300 P_19301 e_19302 f_19303 =>
      match e_19302 in (Eq_0 __19305 __19306 y_19307) return
        (P_19301) y_19307
      with
      | (refl_1 ) => f_19303
      end) :
    (A_19308 : Type) ->
      (x_19309 : A_19308) ->
        (y_19310 : A_19308) ->
          (P_19311 : (A_19308) -> Type) ->
            (e_19313 : (Eq_0 A_19308 x_19309 y_19310)) ->
              (f_19314 : (P_19311) x_19309) -> (P_19311) y_19310).

Definition LnInd_19315 :=
  ((fun A_19316 x_19317 y_19318 P_19319 e_19320 f_19321 =>
      match e_19320 in (Eq_0 __19323 __19324 y_19325) return
        (P_19319) y_19325
      with
      | (refl_1 ) => f_19321
      end) :
    (A_19326 : Type) ->
      (x_19327 : A_19326) ->
        (y_19328 : A_19326) ->
          (P_19329 : (A_19326) -> Linear) ->
            (e_19331 : (Eq_0 A_19326 x_19327 y_19328)) ->
              (f_19332 : (P_19329) x_19327) -> (P_19329) y_19328).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_19334 :=
  ((fix add_19335 m_19336 n_19337 =>
      match m_19336 with
      | (O_7 ) => n_19337
      | (S_8 m_19338) => (S_8 ((add_19335) m_19338) n_19337)
      end) :
    (m_19339 : Nat_6) -> (n_19340 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_19341 : Type) (F_19342 : (A_19341) -> Type) : Type :=
| pair_13 (A_19344 : Type)
            (F_19345 : (A_19344) -> Type)
              : (x_19347 : A_19344) ->
                  ((F_19345) x_19347) -> (Sigma_12 A_19344 F_19345).

Inductive Tensor_14 (A_19349 : Linear) (B_19350 : Linear) : Linear :=
| tpair_15 (A_19351 : Linear)
             (B_19352 : Linear)
               : (A_19351) -> (B_19352) -> (Tensor_14 A_19351 B_19352).

Inductive FTensor_16 (A_19355 : Type)
                       (F_19356 : (A_19355) -> Linear) : Linear :=
| fpair_17 (A_19358 : Type)
             (F_19359 : (A_19358) -> Linear)
               : (x_19361 : A_19358) ->
                   ((F_19359) x_19361) -> (FTensor_16 A_19358 F_19359).

Axiom unsafeC_19363 : (A_19364 : Linear) -> (A_19364) -> Unit_2.

Axiom unsafeP_19366 : (A_19367 : Linear) -> A_19367.

Definition Loc_19368 := ((Nat_6) : Type).

Axiom PtsTo_19369 : (Loc_19368) -> (Type) -> Linear.

Definition Ptr_19372 :=
  ((fun A_19373 =>
      (FTensor_16 Loc_19368 fun l_19374 => ((PtsTo_19369) l_19374) A_19373)) :
    (A_19375 : Type) -> Linear).

Axiom New_19376 : (A_19377 : Type) -> (A_19377) -> (Ptr_19372) A_19377.

Axiom Free_19379 : (A_19380 : Type) -> ((Ptr_19372) A_19380) -> Unit_2.

Axiom Get_19382 :
  (A_19383 : Type) ->
    (l_19384 : Loc_19368) ->
      (((PtsTo_19369) l_19384) A_19383) ->
        (FTensor_16 A_19383 fun __19386 => ((PtsTo_19369) l_19384) A_19383).

Axiom Set_19387 :
  (A_19388 : Type) ->
    (B_19389 : Type) ->
      (B_19389) ->
        (l_19391 : Loc_19368) ->
          (((PtsTo_19369) l_19391) A_19388) ->
            ((PtsTo_19369) l_19391) B_19389.

Axiom ptsto_19393 : (A_19394 : Type) -> (Nat_6) -> (A_19394) -> Linear.

Axiom new_19397 :
  (A_19398 : Type) ->
    (x_19399 : A_19398) ->
      (FTensor_16
        Nat_6 fun l_19400 => (((ptsto_19393) A_19398) l_19400) x_19399).

Axiom free_19401 :
  (A_19402 : Type) ->
    (l_19403 : Nat_6) ->
      (x_19404 : A_19402) ->
        ((((ptsto_19393) A_19402) l_19403) x_19404) -> Unit_2.

Axiom get_19406 :
  (A_19407 : Type) ->
    (l_19408 : Nat_6) ->
      (x_19409 : A_19407) ->
        ((((ptsto_19393) A_19407) l_19408) x_19409) ->
          (FTensor_16
            (Sigma_12 A_19407 fun y_19411 => (Eq_0 A_19407 x_19409 y_19411))
              fun __19412 => (((ptsto_19393) A_19407) l_19408) x_19409).

Axiom set_19413 :
  (A_19414 : Type) ->
    (B_19415 : Type) ->
      (l_19416 : Nat_6) ->
        (x_19417 : A_19414) ->
          ((((ptsto_19393) A_19414) l_19416) x_19417) ->
            (y_19419 : B_19415) -> (((ptsto_19393) B_19415) l_19416) y_19419.

Definition main_19420 :=
  ((let x_19421 := ((new_19397) Nat_6) (S_8 O_7) in
    match x_19421 with
    | (fpair_17 __19422 c_19423) =>
      let x_19424 := ((((get_19406) Nat_6) __19422) (S_8 O_7)) c_19423 in
      match x_19424 with
      | (fpair_17 xeq_19425 c_19426) =>
        let x_19427 := ((((get_19406) Nat_6) __19422) (S_8 O_7)) c_19426 in
        match x_19427 with
        | (fpair_17 yeq_19428 c_19429) =>
          let x_19430 := xeq_19425 in
          match x_19430 with
          | (pair_13 x_19431 pf1_19432) =>
            let x0_19433 := yeq_19428 in
            match x0_19433 with
            | (pair_13 y_19434 pf2_19435) =>
              let pf1_19436 :=
                ((((Eq_sym_19284) Nat_6) (S_8 O_7)) x_19431) pf1_19432
              in
              let pf_19437 :=
                ((((((((Eq_trans_19267) Nat_6) x_19431) (S_8 O_7)) y_19434)
                     pf1_19436)
                    pf2_19435) :
                  (Eq_0 Nat_6 x_19431 y_19434))
              in
              let c_19438 :=
                ((((((set_19413) Nat_6) Nat_6) __19422) (S_8 O_7)) c_19429)
                  (S_8 (S_8 O_7))
              in
              let x0_19439 :=
                ((((get_19406) Nat_6) __19422) (S_8 (S_8 O_7))) c_19438
              in
              match x0_19439 with
              | (fpair_17 zeq_19440 c_19441) =>
                let x0_19442 := zeq_19440 in
                match x0_19442 with
                | (pair_13 z_19443 pf3_19444) =>
                  let pf_19445 :=
                    ((pf3_19444) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_19443))
                  in ((((free_19401) Nat_6) __19422) (S_8 (S_8 O_7))) c_19441
                end
              end
            end
          end
        end
      end
    end) : Unit_2).



match ((new_26) Nat_6) (S_8 O_7) with
| (fpair_17 __19767 c_19768) =>
  let x_19769 := ((((get_28) Nat_6) __19767) (S_8 O_7)) c_19768 in
  match x_19769 with
  | (fpair_17 xeq_19770 c_19771) =>
    let x_19772 := ((((get_28) Nat_6) __19767) (S_8 O_7)) c_19771 in
    match x_19772 with
    | (fpair_17 yeq_19773 c_19774) =>
      let x_19775 := xeq_19770 in
      match x_19775 with
      | (pair_13 x_19776 pf1_19777) =>
        let x0_19778 := yeq_19773 in
        match x0_19778 with
        | (pair_13 y_19779 pf2_19780) =>
          let pf1_19781 :=
            ((((fun A_19782 x_19783 y_19784 e_19785 =>
                  match e_19785 in (Eq_0 __19787 __19788 y_19789) return
                    (Eq_0 A_19782 y_19789 x_19783)
                  with
                  | (refl_1 ) => refl_1
                  end)
                 Nat_6)
                (S_8 O_7))
               x_19776)
              pf1_19777
          in
          let pf_19790 :=
            ((((((((fun A_19791 x_19792 y_19793 z_19794 e1_19795 e2_19796 =>
                      match e2_19796 in (Eq_0 __19798 __19799 y_19800) return
                        (Eq_0 A_19791 x_19792 y_19800)
                      with
                      | (refl_1 ) => e1_19795
                      end)
                     Nat_6)
                    x_19776)
                   (S_8 O_7))
                  y_19779)
                 pf1_19781)
                pf2_19780) :
              (Eq_0 Nat_6 x_19776 y_19779))
          in
          let c_19801 :=
            ((((((set_29) Nat_6) Nat_6) __19767) (S_8 O_7)) c_19774)
              (S_8 (S_8 O_7))
          in
          let x0_19802 :=
            ((((get_28) Nat_6) __19767) (S_8 (S_8 O_7))) c_19801
          in
          match x0_19802 with
          | (fpair_17 zeq_19803 c_19804) =>
            let x0_19805 := zeq_19803 in
            match x0_19805 with
            | (pair_13 z_19806 pf3_19807) =>
              let pf_19808 :=
                ((pf3_19807) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_19806))
              in ((((free_27) Nat_6) __19767) (S_8 (S_8 O_7))) c_19804
            end
          end
        end
      end
    end
  end
end

