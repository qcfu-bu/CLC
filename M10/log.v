parse ok
desugar ok
elab ok
resolve ok
tcheck ok
Inductive Eq_0 (A_15138 : Type) (x_15139 : A_15138) : (A_15138) -> Type :=
| refl_1 (A_15141 : Type)
           (x_15142 : A_15141) : (Eq_0 A_15141 x_15142 x_15142).

Definition Eq_trans_15143 :=
  ((fun A_15144 x_15145 y_15146 z_15147 e1_15148 e2_15149 =>
      match e2_15149 in (Eq_0 __15151 __15152 y_15153) return
        (Eq_0 A_15144 x_15145 y_15153)
      with
      | (refl_1 ) => e1_15148
      end) :
    (A_15154 : Type) ->
      (x_15155 : A_15154) ->
        (y_15156 : A_15154) ->
          (z_15157 : A_15154) ->
            (e1_15158 : (Eq_0 A_15154 x_15155 y_15156)) ->
              (e2_15159 : (Eq_0 A_15154 y_15156 z_15157)) ->
                (Eq_0 A_15154 x_15155 z_15157)).

Definition Eq_sym_15160 :=
  ((fun A_15161 x_15162 y_15163 e_15164 =>
      match e_15164 in (Eq_0 __15166 __15167 y_15168) return
        (Eq_0 A_15161 y_15168 x_15162)
      with
      | (refl_1 ) => refl_1
      end) :
    (A_15169 : Type) ->
      (x_15170 : A_15169) ->
        (y_15171 : A_15169) ->
          (e_15172 : (Eq_0 A_15169 x_15170 y_15171)) ->
            (Eq_0 A_15169 y_15171 x_15170)).

Definition TyInd_15173 :=
  ((fun A_15174 x_15175 y_15176 P_15177 e_15178 f_15179 =>
      match e_15178 in (Eq_0 __15181 __15182 y_15183) return
        (P_15177) y_15183
      with
      | (refl_1 ) => f_15179
      end) :
    (A_15184 : Type) ->
      (x_15185 : A_15184) ->
        (y_15186 : A_15184) ->
          (P_15187 : (A_15184) -> Type) ->
            (e_15189 : (Eq_0 A_15184 x_15185 y_15186)) ->
              (f_15190 : (P_15187) x_15185) -> (P_15187) y_15186).

Definition LnInd_15191 :=
  ((fun A_15192 x_15193 y_15194 P_15195 e_15196 f_15197 =>
      match e_15196 in (Eq_0 __15199 __15200 y_15201) return
        (P_15195) y_15201
      with
      | (refl_1 ) => f_15197
      end) :
    (A_15202 : Type) ->
      (x_15203 : A_15202) ->
        (y_15204 : A_15202) ->
          (P_15205 : (A_15202) -> Linear) ->
            (e_15207 : (Eq_0 A_15202 x_15203 y_15204)) ->
              (f_15208 : (P_15205) x_15203) -> (P_15205) y_15204).

Inductive Unit_2 : Type :=
| tt_3 : Unit_2.

Inductive Base_4 : Linear :=
| ll_5 : Base_4.

Inductive Nat_6 : Type :=
| O_7 : Nat_6
| S_8 : (Nat_6) -> Nat_6.

Definition add_15210 :=
  ((fix add_15211 m_15212 n_15213 =>
      match m_15212 with
      | (O_7 ) => n_15213
      | (S_8 m_15214) => (S_8 ((add_15211) m_15214) n_15213)
      end) :
    (m_15215 : Nat_6) -> (n_15216 : Nat_6) -> Nat_6).

Inductive Bool_9 : Type :=
| true_10 : Bool_9
| false_11 : Bool_9.

Inductive Sigma_12 (A_15217 : Type) (F_15218 : (A_15217) -> Type) : Type :=
| pair_13 (A_15220 : Type)
            (F_15221 : (A_15220) -> Type)
              : (x_15223 : A_15220) ->
                  ((F_15221) x_15223) -> (Sigma_12 A_15220 F_15221).

Inductive Tensor_14 (A_15225 : Linear) (B_15226 : Linear) : Linear :=
| tpair_15 (A_15227 : Linear)
             (B_15228 : Linear)
               : (A_15227) -> (B_15228) -> (Tensor_14 A_15227 B_15228).

Inductive FTensor_16 (A_15231 : Type)
                       (F_15232 : (A_15231) -> Linear) : Linear :=
| fpair_17 (A_15234 : Type)
             (F_15235 : (A_15234) -> Linear)
               : (x_15237 : A_15234) ->
                   ((F_15235) x_15237) -> (FTensor_16 A_15234 F_15235).

Axiom unsafeC_15239 : (A_15240 : Linear) -> (A_15240) -> Unit_2.

Axiom unsafeP_15242 : (A_15243 : Linear) -> A_15243.

Definition Loc_15244 := ((Nat_6) : Type).

Axiom PtsTo_15245 : (Loc_15244) -> (Type) -> Linear.

Definition Ptr_15248 :=
  ((fun A_15249 =>
      (FTensor_16 Loc_15244 fun l_15250 => ((PtsTo_15245) l_15250) A_15249)) :
    (A_15251 : Type) -> Linear).

Axiom New_15252 : (A_15253 : Type) -> (A_15253) -> (Ptr_15248) A_15253.

Axiom Free_15255 : (A_15256 : Type) -> ((Ptr_15248) A_15256) -> Unit_2.

Axiom Get_15258 :
  (A_15259 : Type) ->
    (l_15260 : Loc_15244) ->
      (((PtsTo_15245) l_15260) A_15259) ->
        (FTensor_16 A_15259 fun __15262 => ((PtsTo_15245) l_15260) A_15259).

Axiom Set_15263 :
  (A_15264 : Type) ->
    (B_15265 : Type) ->
      (B_15265) ->
        (l_15267 : Loc_15244) ->
          (((PtsTo_15245) l_15267) A_15264) ->
            ((PtsTo_15245) l_15267) B_15265.

Axiom ptsto_15269 : (A_15270 : Type) -> (Nat_6) -> (A_15270) -> Linear.

Axiom new_15273 :
  (A_15274 : Type) ->
    (x_15275 : A_15274) ->
      (FTensor_16
        Nat_6 fun l_15276 => (((ptsto_15269) A_15274) l_15276) x_15275).

Axiom free_15277 :
  (A_15278 : Type) ->
    (l_15279 : Nat_6) ->
      (x_15280 : A_15278) ->
        ((((ptsto_15269) A_15278) l_15279) x_15280) -> Unit_2.

Axiom get_15282 :
  (A_15283 : Type) ->
    (l_15284 : Nat_6) ->
      (x_15285 : A_15283) ->
        ((((ptsto_15269) A_15283) l_15284) x_15285) ->
          (FTensor_16
            (Sigma_12 A_15283 fun y_15287 => (Eq_0 A_15283 x_15285 y_15287))
              fun __15288 => (((ptsto_15269) A_15283) l_15284) x_15285).

Axiom set_15289 :
  (A_15290 : Type) ->
    (B_15291 : Type) ->
      (l_15292 : Nat_6) ->
        (x_15293 : A_15290) ->
          ((((ptsto_15269) A_15290) l_15292) x_15293) ->
            (y_15295 : B_15291) -> (((ptsto_15269) B_15291) l_15292) y_15295.

Definition main_15296 :=
  ((let x_15297 := ((new_15273) Nat_6) (S_8 O_7) in
    match x_15297 with
    | (fpair_17 __15298 c_15299) =>
      let x_15300 := ((((get_15282) Nat_6) __15298) (S_8 O_7)) c_15299 in
      match x_15300 with
      | (fpair_17 xeq_15301 c_15302) =>
        let x_15303 := ((((get_15282) Nat_6) __15298) (S_8 O_7)) c_15302 in
        match x_15303 with
        | (fpair_17 yeq_15304 c_15305) =>
          let x_15306 := xeq_15301 in
          match x_15306 with
          | (pair_13 x_15307 pf1_15308) =>
            let x0_15309 := yeq_15304 in
            match x0_15309 with
            | (pair_13 y_15310 pf2_15311) =>
              let pf1_15312 :=
                ((((Eq_sym_15160) Nat_6) (S_8 O_7)) x_15307) pf1_15308
              in
              let pf_15313 :=
                ((((((((Eq_trans_15143) Nat_6) x_15307) (S_8 O_7)) y_15310)
                     pf1_15312)
                    pf2_15311) :
                  (Eq_0 Nat_6 x_15307 y_15310))
              in
              let c_15314 :=
                ((((((set_15289) Nat_6) Nat_6) __15298) (S_8 O_7)) c_15305)
                  (S_8 (S_8 O_7))
              in
              let x0_15315 :=
                ((((get_15282) Nat_6) __15298) (S_8 (S_8 O_7))) c_15314
              in
              match x0_15315 with
              | (fpair_17 zeq_15316 c_15317) =>
                let x0_15318 := zeq_15316 in
                match x0_15318 with
                | (pair_13 z_15319 pf3_15320) =>
                  let pf_15321 :=
                    ((pf3_15320) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_15319))
                  in ((((free_15277) Nat_6) __15298) (S_8 (S_8 O_7))) c_15317
                end
              end
            end
          end
        end
      end
    end) : Unit_2).



match ((new_26) Nat_6) (S_8 O_7) with
| (fpair_17 __15643 c_15644) =>
  let x_15645 := ((((get_28) Nat_6) __15643) (S_8 O_7)) c_15644 in
  match x_15645 with
  | (fpair_17 xeq_15646 c_15647) =>
    let x_15648 := ((((get_28) Nat_6) __15643) (S_8 O_7)) c_15647 in
    match x_15648 with
    | (fpair_17 yeq_15649 c_15650) =>
      let x_15651 := xeq_15646 in
      match x_15651 with
      | (pair_13 x_15652 pf1_15653) =>
        let x0_15654 := yeq_15649 in
        match x0_15654 with
        | (pair_13 y_15655 pf2_15656) =>
          let pf1_15657 :=
            ((((fun A_15658 x_15659 y_15660 e_15661 =>
                  match e_15661 in (Eq_0 __15663 __15664 y_15665) return
                    (Eq_0 A_15658 y_15665 x_15659)
                  with
                  | (refl_1 ) => refl_1
                  end)
                 Nat_6)
                (S_8 O_7))
               x_15652)
              pf1_15653
          in
          let pf_15666 :=
            ((((((((fun A_15667 x_15668 y_15669 z_15670 e1_15671 e2_15672 =>
                      match e2_15672 in (Eq_0 __15674 __15675 y_15676) return
                        (Eq_0 A_15667 x_15668 y_15676)
                      with
                      | (refl_1 ) => e1_15671
                      end)
                     Nat_6)
                    x_15652)
                   (S_8 O_7))
                  y_15655)
                 pf1_15657)
                pf2_15656) :
              (Eq_0 Nat_6 x_15652 y_15655))
          in
          let c_15677 :=
            ((((((set_29) Nat_6) Nat_6) __15643) (S_8 O_7)) c_15650)
              (S_8 (S_8 O_7))
          in
          let x0_15678 :=
            ((((get_28) Nat_6) __15643) (S_8 (S_8 O_7))) c_15677
          in
          match x0_15678 with
          | (fpair_17 zeq_15679 c_15680) =>
            let x0_15681 := zeq_15679 in
            match x0_15681 with
            | (pair_13 z_15682 pf3_15683) =>
              let pf_15684 :=
                ((pf3_15683) : (Eq_0 Nat_6 (S_8 (S_8 O_7)) z_15682))
              in ((((free_27) Nat_6) __15643) (S_8 (S_8 O_7))) c_15680
            end
          end
        end
      end
    end
  end
end

