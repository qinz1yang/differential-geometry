import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2RowOuts
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2BranchOuts
import DifferentialGeometry.Geometry.Fibration.ActualStageClouds

/-!
# The chapter-14 row fields of the closed validity on the staged register (lane FC39-VAL3)

External review 52 (`docs/geometrization/chapter14/out/dispositions-task52-fc39-threshold-
validity.md`, "Missing obligations to add"): the closed validity record on `ClosedRegisterV2`
carries, for every instance of the final family at a staged register `R`, the NATIVE conclusions of
the chapter-14 rows at the register's values (no substitution), the early graph constants of the
actual graph producers, and the producer's scale conditions.

* `ClosedRowOutsV2 F`: on the family `F.family : LocalChartPacketsC14 …` of an instance at `R` (each
  row on the projection it is stated on), the conclusions of TCP01 (Gram), TCP02, TCP03 (zero
  block), TCP04, TCP05, TCP06; EGP03, EGP04, EGP06, EGP07; SGP01, SGP02, SGP03 (zero block),
  SGP04, SGP06, at the tolerances (decisions D6 of FC39-VAL2): TCP02 / EGP03 / SGP02 at the long
  raw error `E` of the circle requests; TCP03 and TCP04 at `θ₂`; EGP04 at `θ_e`; SGP03 at `θ_s`
  with accuracy `θ_s²/(2·10⁶)`; the graph rows and the branch ends at the stage values
  `(Γ_j, Σ_j, e_j)` (`j = 0` circle, `1` edge, `2` slim).
* `ClosedScaleBudgetV2 R`: the scale conditions of `eventually_nonempty_localChartPacketsC14` on `Λ`
  at the register's values (`Δ, ε, τ, s', γc`).
* `PartialClosedThresholdValidityV2Rows`: the core record of FC39-VAL2 G2a extended by `C_ge`
  (`gafGraphConst j ≤ C_j`: the constants of TCP05, EGP06, SGP04 below the early `C`), the scale
  budget at every staged register, and the row fields on every instance with `εr < ε₀` and
  `20 Λz ≤ T₀`. Still PARTIAL (review 52 naming): `Nb`, `cw` on the actual stage clouds, the native
  LFR29.1 `W` adapter, the endpoint model and end buffer, `RowsAt` v2 and boundary validity are
  not fields yet.
* Consumers: `exists_family_rows_on_tail_VAL3` (one tail on which every member carries an instance
  with ALL row conclusions), `ClosedStage.stage_range_VAL3` and the branch-end ranges
  `tcp06_range_VAL3`, `egp07_range_VAL3`, `sgp06_range_VAL3` (the stage values meet (TP), (EP),
  (CP) once `C_ge` holds), `tcp_scale_budget_VAL3` (TCP05/TCP06's `1000CΔΛ < e`),
  `twelve_hundred_le_Δ_VAL3`, and `graph_derivative_le_C_VAL3` (the actual circle graph model's
  derivatives are bounded by the early `C₀`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The chapter-14 row conclusions on one instance of the final family at `R`**, at the
register's values (each row on the projection of `F.family` it is stated on). -/
def ClosedRowOutsV2 {K : ℕ} {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    {R : ClosedRegisterV2 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV2 K R M δ εr Λz) : Prop :=
  Tcp01GramOutV2 F.family.toLocalChartPackets ∧
  Tcp02OutV2 F.family.toLocalChartPackets R.later.circle.E ∧
  Tcp03ZeroOutV2 F.family.toLocalChartPacketsZ R.later.circle.θ₂ ∧
  Tcp04OutV2 F.family.toLocalChartPackets R.later.circle.θ₂ ∧
  Tcp05OutV2 F.family (R.stage.e 0) ∧
  Tcp06OutV2 F.family (R.stage.Γ 0) (R.stage.Sig 0) (R.stage.e 0) ∧
  Egp03OutV2 F.family.toLocalChartFamilyE R.later.circle.E ∧
  Egp04OutV2 F.family.toLocalChartPacketsRVZ R.later.circle.θe ∧
  Egp06OutV2 F.family.toLocalChartPacketsRVZ (R.stage.e 1) ∧
  Egp07OutV2 F.family (R.stage.Γ 1) (R.stage.Sig 1) (R.stage.e 1) ∧
  Sgp01OutV2 F.family.toLocalChartPacketsR ∧
  Sgp02OutV2 F.family.toLocalChartFamilyQ R.later.circle.E ∧
  Sgp03ZeroOutV2 F.family.toLocalChartPacketsRVZ R.later.circle.θs
    (R.later.circle.θs ^ 2 / (2 * 10 ^ 6)) ∧
  Sgp04OutV2 F.family.toLocalChartPacketsRVZ (R.stage.e 2) ∧
  Sgp06OutV2 F.family (R.stage.Γ 2) (R.stage.Sig 2) (R.stage.e 2)

/-- **The producer's scale conditions at `R`** (`eventually_nonempty_localChartPacketsC14`, the
conditions on `Λ`, verbatim, at the register's `Δ, ε, τ, s', γc`). -/
def ClosedScaleBudgetV2 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (R : ClosedRegisterV2 D T) : Prop :=
  R.later.excl.Δ * R.later.scale.Λ * 2000000 ≤ 1 / 100 ∧
  R.later.scale.Λ < 1 / (1000000 * R.later.excl.Δ) ∧
  100 * R.later.excl.Δ * R.later.scale.Λ ≤ 1 / 1000000 ∧
  2 * R.later.err.co.ε + 300 * R.later.excl.Δ * R.later.scale.Λ +
      Real.sqrt (504000 / R.later.excl.Δ + 3780 * R.later.err.bd.τ) < R.later.circle.γc / 1000 ∧
  R.later.scale.Λ < R.later.err.wk.s' / (100000000 * R.later.excl.Δ ^ 2) ∧
  100 * R.later.excl.Δ * R.later.scale.Λ ≤ 1 / 10 ^ 8

/-- **The closed threshold validity on the staged register with the chapter-14 row fields**
(review 52; still PARTIAL: `Nb`, `cw` on the actual stage clouds, the native LFR29.1 `W` adapter,
the endpoint model and end buffer are open statements, `RowsAt` v2 and boundary validity wait). -/
structure PartialClosedThresholdValidityV2Rows (K : ℕ) (A : ℝ → ℝ)
    (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (D : ClosedEarlyData) (T : ClosedThresholdsV2 D) : Prop
    extends PartialClosedThresholdValidityV2 K A Wseq gseq D T where
  /-- PR01 `C`: the early graph constants of the actual graph producers TCP05, EGP06, SGP04
  (`gafGraphConst`, index `0` circle, `1` edge, `2` slim) are below `C_j`. -/
  C_ge : ∀ j, gafGraphConst j ≤ D.C j
  /-- PR19 `scaleUp`: the producer's scale conditions at every staged register. -/
  scale_budget : ∀ R : ClosedRegisterV2 D T, ClosedScaleBudgetV2 R
  /-- PR11–PR25: the chapter-14 row conclusions on every instance of the final family at every
  staged register, at the register's values, for every `εr` below the cap and `20 Λz ≤ T₀`. -/
  rows : ∀ (R : ClosedRegisterV2 D T) (δ εr Λz : ℝ), εr < R.later.err.co.ε₀ →
    20 * Λz ≤ R.later.split.T₀ → ∀ m (M : ClosedModel (Wseq m) (gseq m))
    (F : ClosedFamilyInstanceV2 K R M δ εr Λz), ClosedRowOutsV2 F

namespace PartialClosedThresholdValidityV2Rows

variable {K : ℕ} {A : ℝ → ℝ} {Wseq : ℕ → CompactCarrier.{u}}
  {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier}
  {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}

/-- **Consumer (single certificate with the rows)**: at every staged register, one tail
`N ≥ R.later.tail` on which every member carries an instance of the final family at `R` whose
chapter-14 row conclusions ALL hold at the register's values, with `20 Λz ≤ T₀` and `εr < ε₀`. -/
theorem exists_family_rows_on_tail_VAL3
    (hv : PartialClosedThresholdValidityV2Rows K A Wseq gseq D T)
    (hf : ∀ m, ClosedMemberFacts (Wseq m)) (R : ClosedRegisterV2 D T) :
    ∃ N : ℕ, R.later.tail ≤ N ∧ ∃ δ εr Λz : ℝ, 20 * Λz ≤ R.later.split.T₀ ∧
      εr < R.later.err.co.ε₀ ∧ ∀ m, N ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
        ∃ F : ClosedFamilyInstanceV2 K R M δ εr Λz, ClosedRowOutsV2 F := by
  obtain ⟨εrF, δ'F, ΛzF, h⟩ := hv.family hf
  obtain ⟨-, -, hcap, -, -, hT, δ, -, -, ht⟩ := h R
  have hT₀ := hT.trans ((le_max_right _ _).trans R.later.T₀_ge)
  refine ⟨R.later.tail, le_rfl, δ, _, _, hT₀, hcap, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  exact ⟨M, F, hv.rows R δ _ _ hcap hT₀ m M F⟩

/-- **Consumer (`early.C` on the actual circle graph model)**: on every instance at `R` with the row
conclusions, every circle centre carries TCP05's actual graph model `Φ` with `‖DΦ‖, ‖D²Φ‖ ≤ C₀`
and (TG) at the stage accuracy `e₀`. -/
theorem graph_derivative_le_C_VAL3
    (hv : PartialClosedThresholdValidityV2Rows K A Wseq gseq D T) {R : ClosedRegisterV2 D T}
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g}
    {δ εr Λz : ℝ} (F : ClosedFamilyInstanceV2 K R M δ εr Λz) (hF : ClosedRowOutsV2 F) (i : M.X)
    (hi : i ∈ F.family.circle.centres) :
    ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag F.family.toLocalChartFamily F.family.zero => ℝ²),
      ContDiff ℝ ∞ Φ ∧ ∀ a, ‖fderiv ℝ Φ a‖ ≤ D.C 0 ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ D.C 0 := by
  obtain ⟨Φ, hΦ, -, hb, -⟩ := hF.2.2.2.2.1 i hi
  have hC : tcpGraphConst ≤ D.C 0 := hv.C_ge 0
  exact ⟨Φ, hΦ, fun a => ⟨(hb a).1.trans hC, (hb a).2.trans hC⟩⟩

end PartialClosedThresholdValidityV2Rows

/-- **Consumer (stage ranges)**: once `C_ge` holds, every stage value `(Γ_j, Σ_j, e_j)` of a closed
stage meets the cloud ranges (TP), (EP), (CP) of the three branch ends with `C = gafGraphConst j`,
and `e_j < Σ_j/1000`. -/
theorem ClosedStage.stage_range_VAL3 {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j)
    (st : ClosedStage D) (j : Fin 3) :
    0 < st.Γ j ∧ st.Γ j < 1 ∧ 0 < st.Sig j ∧ st.Sig j < st.Γ j / 200 ∧
      st.Sig j < st.Γ j ^ 3 / (100 * gafGraphConst j) ∧ 0 < st.e j ∧ st.e j < 1 / 100 ∧
      st.e j < st.Γ j * st.Sig j / 100 ∧ st.e j < st.Sig j / 1000 := by
  have hΓ := st.Γ_pos j
  have hS := st.Sig_lt j
  have he := st.e_lt j
  have hc2 : st.c 2 < 1 := st.c₃_lt_audit.trans (by norm_num)
  have hc1 : st.c 1 ≤ st.c 2 := st.c₂_le.trans (min_le_left _ _)
  have hc0 : st.c 0 ≤ st.c 1 := st.c₁_le.trans (min_le_left _ _)
  have hcj : st.c j < 1 := by
    fin_cases j
    · exact (hc0.trans hc1).trans_lt hc2
    · exact hc1.trans_lt hc2
    · exact hc2
  have hΓ1 : st.Γ j < 1 := (st.Γ_le j).trans_lt (by linarith [st.c_pos j])
  have hG : 0 < gafGraphConst j := by
    fin_cases j
    · exact zero_lt_one.trans_le one_le_tcpGraphConst
    · exact egpGraphConst_pos_KC4
    · exact (by norm_num : (0 : ℝ) < 4000).trans_le four_le_sgpGraphBound_SGP4
  have hCG : st.Γ j ^ 3 / (100 * D.C j) ≤ st.Γ j ^ 3 / (100 * gafGraphConst j) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (hC j) (by norm_num))
  simp only [closedSigmaBound, lt_min_iff] at hS
  simp only [closedErrorBound, lt_min_iff] at he
  exact ⟨hΓ, hΓ1, st.Sig_pos j, hS.2.2.1, hS.2.2.2.trans_le hCG, st.e_pos j, he.1, he.2.1,
    he.2.2.1⟩

/-- TCP06's cloud range (TP) at the circle stage values (`C = tcpGraphConst`). -/
theorem ClosedStage.tcp06_range_VAL3 {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j)
    (st : ClosedStage D) :
    0 < st.Γ 0 ∧ st.Γ 0 < 1 ∧ 0 < st.Sig 0 ∧ st.Sig 0 < st.Γ 0 / 200 ∧
      st.Sig 0 < st.Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ 0 < st.e 0 ∧ st.e 0 < 1 / 100 ∧
      st.e 0 < st.Γ 0 * st.Sig 0 / 100 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := st.stage_range_VAL3 hC 0
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- EGP07's cloud range (EP) at the edge stage values, in `egp07_row_C14`'s `min` form. -/
theorem ClosedStage.egp07_range_VAL3 {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j)
    (st : ClosedStage D) :
    st.Γ 1 ∈ Ioo (0 : ℝ) 1 ∧ 0 < st.Sig 1 ∧
      st.Sig 1 < min (st.Γ 1 / 200) (st.Γ 1 ^ 3 / (100 * egpGraphConst)) ∧ 0 < st.e 1 ∧
      st.e 1 < min (1 / 100) (min (st.Γ 1 * st.Sig 1 / 100) (st.Sig 1 / 1000)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := st.stage_range_VAL3 hC 1
  exact ⟨⟨h1, h2⟩, h3, lt_min h4 h5, h6, lt_min h7 (lt_min h8 h9)⟩

/-- SGP06's cloud range (CP) at the slim stage values (`C_* = sgpGraphBound`). -/
theorem ClosedStage.sgp06_range_VAL3 {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j)
    (st : ClosedStage D) :
    0 < st.Γ 2 ∧ st.Γ 2 < 1 ∧ 0 < st.Sig 2 ∧ st.Sig 2 < st.Γ 2 / 200 ∧
      st.Sig 2 < st.Γ 2 ^ 3 / (100 * sgpGraphBound) ∧ 0 < st.e 2 ∧ st.e 2 < 1 / 100 ∧
      st.e 2 < st.Γ 2 * st.Sig 2 / 100 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := st.stage_range_VAL3 hC 2
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **Consumer (TCP05/TCP06's scale request)**: at every staged register, once `C_ge` holds,
`1000 · tcpGraphConst · Δ · Λ < e₀` at the register's `Δ, Λ` and the circle stage accuracy. -/
theorem ClosedRegisterV2.tcp_scale_budget_VAL3 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (hC : ∀ j, gafGraphConst j ≤ D.C j) (R : ClosedRegisterV2 D T) :
    1000 * tcpGraphConst * R.later.excl.Δ * R.later.scale.Λ < R.stage.e 0 := by
  have hreg := R.later.regScale_e
  have hC0 := D.C_pos 0
  have hΔΛ : 0 ≤ R.later.excl.Δ * R.later.scale.Λ :=
    mul_nonneg R.later.Δ_pos_VAL2.le R.later.Λ_pos.le
  have hT : tcpGraphConst ≤ D.C 0 := hC 0
  rw [lt_div_iff₀ (by positivity)] at hreg
  calc 1000 * tcpGraphConst * R.later.excl.Δ * R.later.scale.Λ
      = 1000 * tcpGraphConst * (R.later.excl.Δ * R.later.scale.Λ) := by ring
    _ ≤ 1000 * D.C 0 * (R.later.excl.Δ * R.later.scale.Λ) := by gcongr
    _ = R.later.excl.Δ * R.later.scale.Λ * (1000 * D.C 0) := by ring
    _ < R.stage.e 0 := hreg

/-- **Consumer (`ΔLow`)**: the register's `Δ` meets TCP04–TCP06's `Δ ≥ 1200`. -/
theorem ClosedLaterV2.twelve_hundred_le_Δ_VAL3 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    {st : ClosedStage D} (la : ClosedLaterV2 D T st) : 1200 ≤ la.excl.Δ := by
  have h := la.Δ_gt
  have h1 : (10 : ℝ) ^ 6 < la.excl.Δ := (le_max_left _ _).trans_lt h
  linarith

end DifferentialGeometry.Geometry.Collapse
