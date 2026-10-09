import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyWithChoiceBSTD2

/-!
# Register-level numerics of the boundary rows BCG04 / BCG05 / BCG06, F1 and N76-9 (S-REG-NUM2, G4)

Lane S-REG-NUM2 (`_RNUM`), group G4, part 1 (register side; the row consumers are in
`BoundaryRegisterRowNumericsApplicationsRNUM`). The boundary rows `bcg04_05_06_rows_final_BGR`
(G33), BCG07 F1 (`rim_mem_source_zero_OF1`) and the open-edge parent
(`exists_edgeParent_of_core_BAUGD`) carry numerical premises on the register's parameters. Here each
one is read off the register of lane BSTD2, with NO new field and NO new structure.

## Audit table: premise -> choice node -> supplier

* `0 < r_∂` ← `R.rd_pos`.
* `r_∂ < 1/10000` ← `R.rd_phys` (`boundaryPhysicalBound` has the term `1/10⁴`):
  `BoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM`.
* `20 (c₂ + 1) r_∂ < 10⁻⁶` (`c₂ = c 2` of the CHOICE): two suppliers.
  (a) `rd_mul_lt_of_le_RNUM`: from `R.rd_phys` (the term `10⁻⁶/(20 (c₃ + 1))`) and `c₂ ≤ c₃` —
  the early constant `c₃` is NOT tied to the CHOICE's `c 2` by any field (PENDING field
  `c₃ ≥ c 2`, only needed for this supplier);
  (b) NO FIELD NEEDED: the late request `r_∂ ≤ Rq.rd` of `BoundaryLateRequests_BSTD1` (legal: the
  request reads only earlier nodes, here the CHOICE constant `c₂`): `bdryRdRequest_RNUM c₂`,
  `rd_mul_lt_of_request_RNUM`.
* the member premise (N76-3) `1000 δ_{n+1}² < w/(2 (1 + 2Λ⁻¹)³) min(1/2, r_∂/4)²` ← the second
  conjunct of `BoundaryMemberOutput_BSTD1` (a clause of the tail member, taken after `r_∂`).
* `θ < 1/100` ← `EW.θ_lt` (and `ϑ_min = θ`, `EW.ϑmin_eq`).
* `e ≤ 1/1000` (N76-6; ZSP02 on the boundary chain) ← the prefix `P : C14PreFinal` of the producer
  (`P.e_lt3`); the early choices are produced with `∃ P, … ∧ E.toBoundaryEarlyParams_BSTD1 =
  P.toBdryParams_BSTD1`: `exists_boundaryEarlyWithChoice_rows_RNUM`. NOT derivable from the bare
  structure `BoundaryEarlyOver_BSTD1` (`e_lt : e < 1/40` only): PENDING field `e_lt_milli` for
  consumers that do not go through the producer.
* `C_ρ Λ Δ < 10⁻⁶` with `C_ρ = 100 (b_der + 1)(1 + b_cut + c_w(0)/Σ₀)` (N76-9, `hC`) ← the upper
  request `Λ ≤ Rq.Λ` of `C14StagedRequestsSTG` read at `C14PreEdge` (which contains `Δ`):
  `bdryRowRequests_RNUM C_ρ`, `hC_of_request_RNUM`, `exists_boundaryEarlyWithChoice_rows_RNUM`.
  No field needed (the constants `b_der`, `b_cut` are numerical, `c_w, Σ` come from the CHOICE).
* the producer's prefix does NOT carry `3 β_c ≤ β₂` (F1's first premise): the BSTD2 producers drop
  the conjunct (see the handover note); PENDING (field `three_βc_le_β₂` at node `β₂ Δ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

/-! ### The requests (legal: each reads only earlier nodes) -/

/-- **The late request on `r_∂` for BCG06's `20 (c₂ + 1) r_∂ < 10⁻⁶`**:
`r_∂ ≤ 1/(4·10⁷ (|c₂| + 1))` (a constant read after the CHOICE constant `c₂`; the other late
requests are trivial). -/
def bdryRdRequest_RNUM (c2 : ℝ) : BoundaryLateRequests_BSTD1 :=
  { BoundaryLateRequests_BSTD1.trivial with
    rd := fun _ _ _ _ _ _ => 1 / (40000000 * (|c2| + 1))
    rd_pos := fun _ _ _ _ _ _ => by positivity }

/-- **The staged request on `Λ` for N76-9's `C_ρ Λ Δ < 10⁻⁶`**:
`Λ ≤ 1/(2·10⁶ (|C_ρ| + 1)(|Δ| + 1))`, read at the prefix `C14PreEdge` (which contains `Δ`); every
other request is trivial. -/
def bdryRowRequests_RNUM (Cρ : ℝ) : C14StagedRequestsSTG :=
  { C14StagedRequestsSTG.trivial with
    Λ := fun p => 1 / (2 * 10 ^ 6 * (|Cρ| + 1) * (|p.Δ| + 1))
    Λ_pos := fun _ => by positivity }

/-! ### Register facts on `r_∂` -/

namespace BoundaryRegisterOver_BSTD1

variable {Θ : BoundaryProducerThresholds_BSTD1} {E : BoundaryEarlyOver_BSTD1 Θ} {V : ℝ}
  (R : BoundaryRegisterOver_BSTD1 E V)

/-- BCG05 / BCG06: `r_∂ < 1/10000` (`R.rd_phys`: `boundaryPhysicalBound` has the term `1/10⁴`). -/
theorem rd_lt_ten_thousandth_RNUM : R.rd < 1 / 10000 := by
  have h : boundaryPhysicalBound (10 ^ 6 * E.Δ) E.c₃ R.Hd E.ϑ ≤ 1 / 10 ^ 4 := by
    unfold boundaryPhysicalBound
    exact (min_le_right _ _).trans (min_le_left _ _)
  have h2 := R.rd_phys.trans_le h
  have e : (1 : ℝ) / 10 ^ 4 = 1 / 10000 := by norm_num
  rw [e] at h2
  exact h2

/-- BCG06: `20 (c₃ + 1) r_∂ < 10⁻⁶` (`R.rd_phys`: the term `10⁻⁶/(20 (c₃ + 1))`). -/
theorem rd_mul_lt_RNUM : 20 * (E.c₃ + 1) * R.rd < 1 / 1000000 := by
  have hc : 0 < 20 * (E.c₃ + 1) := by
    have := E.c₃_nonneg
    positivity
  have h : boundaryPhysicalBound (10 ^ 6 * E.Δ) E.c₃ R.Hd E.ϑ ≤
      1 / 10 ^ 6 / (20 * (E.c₃ + 1)) := by
    unfold boundaryPhysicalBound
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have h2 := R.rd_phys.trans_le h
  rw [lt_div_iff₀ hc] at h2
  have e : (1 : ℝ) / 10 ^ 6 = 1 / 1000000 := by norm_num
  rw [e] at h2
  linarith

/-- BCG06's `20 (c₂ + 1) r_∂ < 10⁻⁶` for any `c₂ ≤ c₃` (supplier (a): needs `c₂ ≤ c₃`). -/
theorem rd_mul_lt_of_le_RNUM {c2 : ℝ} (hc : c2 ≤ E.c₃) : 20 * (c2 + 1) * R.rd < 1 / 1000000 := by
  have h := R.rd_mul_lt_RNUM
  have hr := R.rd_pos
  nlinarith [mul_nonneg (sub_nonneg.2 hc) hr.le]

/-- BCG06's `20 (c₂ + 1) r_∂ < 10⁻⁶` from the late request `bdryRdRequest_RNUM c₂`
(supplier (b): no field). -/
theorem rd_mul_lt_of_request_RNUM {c2 : ℝ} {V' δ : ℝ}
    (h : R.rd ≤ (bdryRdRequest_RNUM c2).rd V' δ R.Lmax R.βd R.εN R.Hd) :
    20 * (c2 + 1) * R.rd < 1 / 1000000 := by
  have h' : R.rd ≤ 1 / (40000000 * (|c2| + 1)) := h
  rw [le_div_iff₀ (by positivity)] at h'
  have hr := R.rd_pos
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self c2)) hr.le]

end BoundaryRegisterOver_BSTD1

/-! ### The early choice: `e ≤ 1/1000` and `C_ρ Λ Δ < 10⁻⁶` -/

/-- N76-9: a staged prefix meeting `bdryRowRequests_RNUM C_ρ` has `C_ρ Λ Δ < 10⁻⁶`
(`Δ > 10⁶` from the prefix; `Λ ≤ 1/(2·10⁶ (|C_ρ| + 1)(|Δ| + 1))` is the request). -/
theorem hC_of_request_RNUM {Cρ : ℝ} {P : C14PreFinal}
    (hM : (bdryRowRequests_RNUM Cρ).toC14.Meets P) : Cρ * P.Λ * P.Δ < 1 / 1000000 := by
  have h : P.Λ ≤ 1 / (2 * 10 ^ 6 * (|Cρ| + 1) * (|P.Δ| + 1)) := hM.Λ_le
  have hΔ : 0 < P.Δ := by linarith [P.Δ_gt6]
  have hΛ := P.Λ_pos
  have ha : 0 < |Cρ| + 1 := by positivity
  rw [abs_of_pos hΔ] at h
  rw [le_div_iff₀ (by positivity)] at h
  have h1 : Cρ * P.Λ * P.Δ ≤ (|Cρ| + 1) * P.Λ * P.Δ := by
    have : 0 ≤ P.Λ * P.Δ := by positivity
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self Cρ)) this]
  nlinarith [mul_pos ha hΛ]

/-- N76-9 at an early choice: the early choice's parameters are those of a prefix `P` meeting
`bdryRowRequests_RNUM C_ρ`, so `C_ρ Λ Δ < 10⁻⁶`. -/
theorem hC_of_early_request_RNUM {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) {Cρ : ℝ} {P : C14PreFinal}
    (hEP : E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1)
    (hM : (bdryRowRequests_RNUM Cρ).toC14.Meets P) : Cρ * E.Λ * E.Δ < 1 / 1000000 := by
  have eΛ : E.Λ = P.Λ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Λ) hEP
  have eΔ : E.Δ = P.Δ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Δ) hEP
  rw [eΛ, eΔ]
  exact hC_of_request_RNUM hM

/-- N76-6 at an early choice: the early choice's parameters are those of a prefix `P`, and the
prefix carries ZSP's `e < 1/1000` (`P.e_lt3`). -/
theorem e_lt_milli_of_prefix_RNUM {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) {P : C14PreFinal}
    (hEP : E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1) : E.e < 1 / 1000 := by
  have ee : E.e = P.e := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.e) hEP
  rw [ee]
  exact P.e_lt3

/-- **The early choices with the stored CHOICE, with `e < 1/1000` and N76-9** (`hC`): for every
choice `c`, CHI record `χ` with `χ.eg = egOf c`, legal (BA) error and every constant `C_ρ`, a
stored-choice early choice with exactly these data whose `e < 1/1000` (ZSP02 on the boundary chain;
the producer's prefix `P`) and `C_ρ Λ Δ < 10⁻⁶` (the request `bdryRowRequests_RNUM C_ρ`). -/
theorem exists_boundaryEarlyWithChoice_rows_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c)
    {θ νBA : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100) (hθχ : θ ≤ χ.ϑ₀) (hν : 0 < νBA)
    (hν1 : νBA < 1 / 1000000) (hν3 : 3 * νBA ≤ threeSplittingExclusionThreshold.{0, 0})
    (Cρ : ℝ) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ ∧ EW.θ = θ ∧
      EW.νBA = νBA ∧ EW.early.e < 1 / 1000 ∧ Cρ * EW.early.Λ * EW.early.Δ < 1 / 1000000 := by
  obtain ⟨EW, hc, hχ, hθ', hν', P, hM, hEP⟩ :=
    exists_boundaryEarlyWithChoice_of_BSTD2 K hK A hA egOf c χ heg hθ hθ1 hθχ hν hν1 hν3
      (bdryRowRequests_RNUM Cρ)
  exact ⟨EW, hc, hχ, hθ', hν', e_lt_milli_of_prefix_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP,
    hC_of_early_request_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP hM⟩

/-! ### F1 and the open edge parent: the other numerical premises, from the early choice -/

namespace BoundaryEarlyOver_BSTD1

variable {Θ : BoundaryProducerThresholds_BSTD1} (E : BoundaryEarlyOver_BSTD1 Θ)

/-- BCG07 F1's register premises (besides `3 β_c ≤ β₂`, `c₂ < 10⁻⁵` and N76-9):
`β 2 < 1`, `0 ≤ γ`, `γ ≤ 3/4`. -/
theorem f1_numerics_RNUM : E.β 2 < 1 ∧ 0 ≤ E.γ ∧ E.γ ≤ 3 / 4 := by
  refine ⟨?_, E.γ_pos.le, ?_⟩
  · rw [E.β_two]
    linarith [E.β₂_lt]
  · linarith [E.γ_lt]

/-- The numerical premises of the open edge parent `exists_edgeParent_of_core_BAUGD` and of the rim
surjectivity (besides `c₂ < 10⁻⁵` and N76-9): `0 ≤ ε`, `ε < 1`, `0 < γ_c ≤ 1/100`,
`β_c ≤ 10⁻⁵`. -/
theorem edgeParent_numerics_RNUM :
    0 ≤ E.ε ∧ E.ε < 1 ∧ 0 < E.γc ∧ E.γc ≤ 1 / 100 ∧ E.βc ≤ 1 / 100000 := by
  have h1 := E.βc_lt
  have h2 := E.γc_lt
  exact ⟨E.ε_pos.le, by linarith [E.ε_lt], E.γc_pos, h2.le, by linarith⟩

/-- BCG07 F3's `ε_r < 1/2` (the producer's radial output has `ER < 1/4`). -/
theorem εr_lt_half_RNUM : E.εr < 1 / 2 := by
  have h := Θ.ER_lt E.toBdryParamsZero_BSTD1
  unfold BoundaryEarlyOver_BSTD1.εr
  linarith

end BoundaryEarlyOver_BSTD1

/-! ### The register: the row premises on `r_∂`, and the member premise -/

/-- **BCG04 / BCG05 / BCG06 register-level premises** (the row premises of
`bcg04_05_06_rows_final_BGR`, with `θ`, `δ_n`, `w`, `Λ` the stored (BA) error, the member's ratio
and the early constants): for every stored-choice early choice `EW`, every standing sequence `Sq`
and every constant `c₂` (the CHOICE's `c 2`) there are `V`, a register `R` and `n₀` with
`0 < r_∂ < 1/10000`, `20 (c₂ + 1) r_∂ < 10⁻⁶`, and on every member `m ≥ n₀` the member premise
(N76-3) `1000 δ_{m+1}² < w/(2 (1 + 2Λ⁻¹)³) min(1/2, r_∂/4)²`; also `θ < 1/100`. -/
theorem exists_boundaryRegister_rowPremises_RNUM {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar) (c2 : ℝ) :
    EW.θ < 1 / 100 ∧ ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
      0 < R.rd ∧ R.rd < 1 / 10000 ∧ 20 * (c2 + 1) * R.rd < 1 / 1000000 ∧
      ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R ∧
        1000 * boundaryCounterexampleRatio Sq.δ₀ (m + 1) ^ 2 <
          EW.early.w / (2 * (1 + 2 * EW.early.Λ⁻¹) ^ 3) * min (1 / 2) (R.rd / 4) ^ 2 := by
  obtain ⟨V, -, R, -, -, -, -, hrd, n₀, hR⟩ :=
    exists_boundarySequenceAssignmentWC_req_BSTD2 EW Sq (bdryRdRequest_RNUM c2)
  exact ⟨EW.θ_lt, V, R, R.rd_pos, R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM,
    R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd, n₀,
    fun m hm => ⟨hR m hm, (hR m hm).1.1.2⟩⟩

end DifferentialGeometry.Geometry.Collapse
