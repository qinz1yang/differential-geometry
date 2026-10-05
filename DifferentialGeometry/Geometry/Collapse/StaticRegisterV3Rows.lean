import DifferentialGeometry.Geometry.Collapse.StaticRegisterV3RowsCircle
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV3Provenance
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.VolumeLowerEverywhere

/-!
# The partial closed validity on register V3, inhabited (lane FC39-VAL5)

The rows strategies of `StaticRegisterV3RowsStrategy` (11 rows) and `StaticRegisterV3RowsCircle`
(TCP03–TCP06, possible since `β₃` is fixed before PR11) and the producer's scale requests are
combined by the infimum of threshold records; the complete realization of
`StaticRegisterV3Realization` refines the combination. Hence:

* `scaleStrategyV3 D`: the C14 producer's `γc`-budget requests (`ε < γc/8000`,
  `Δ > 504000(4000/γc)²`, `Λ < γc/(1200000Δ)`, `τ < (γc/4000)²/3780`) and LPA02's volume constant
  `I₁ = ∫₀¹ sinh²`; `closedScaleBudgetV3_of_below_VAL5`: the producer's scale conditions at every
  register of a strategy below it (FC39-VAL4's proof).
* `rowsStrategyV3 D = (scale ⊓ 11 rows) ⊓ circle rows`; `rowOuts_of_below_VAL5`: all 15 row
  conclusions on every final family at the register's values; `closedRowOuts_of_below_VAL5`:
  `ClosedRowOutsV3 F` on every instance.
* `exists_closed_realization_rows_VAL5`: ONE common strategy at which every register V3 is realized
  (complete instance: LPA02's joint witness and the zero-ball selection), meets the scale
  conditions, and every instance carries the 15 row conclusions.
* `exists_partialClosedThresholdValidityV3Rows_VAL5`: at the early data `closedEarlyDataShared K`
  (the ONE shared CFS15 modulus), on every closed standing sequence, the record
  `PartialClosedThresholdValidityV3Rows` holds for one strategy — every field discharged. The name
  stays `Partial…` (review 52): the LFR29.1 `W` adapter, the endpoint model and end buffer, the
  TCP01 count, `RowsAt` v2 and boundary validity are not fields of it.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The scale strategy -/

/-- **The scale strategy on register V3**: the C14 producer's `γc`-budget requests and LPA02's
volume constant `I₁ = ∫₀¹ sinh²`; the other slots are `1` (upper), `0` (lower) or trivial. -/
def scaleStrategyV3 (D : ClosedEarlyData) : ClosedThresholdsV3 D where
  Nb := fun _ => 0
  Nb_nonneg := fun _ => le_rfl
  cw := fun _ => 0
  cw_nonneg := fun _ => le_rfl
  lc18 := 1
  lc18_pos := one_pos
  circleUp := fun _ _ _ _ _ => 1
  circleUp_pos := fun _ _ _ _ _ => one_pos
  β₂Up := fun _ _ _ => 1
  β₂Up_pos := fun _ _ _ => one_pos
  ΔLow := fun _ ci _ _ => 504000 * (4000 / ci.γc) ^ 2
  errorsUp := fun _ ci _ => posOr_VAL3 (ci.γc / 8000)
  errorsUp_pos := fun _ _ _ => posOr_pos_VAL3 _
  sectionUp := fun _ ci _ _ => posOr_VAL3 ((ci.γc / 4000) ^ 2 / 3780)
  sectionUp_pos := fun _ _ _ _ => posOr_pos_VAL3 _
  lfr29W := fun _ _ _ _ _ => 1
  lfr29W_pos := fun _ _ _ _ _ => one_pos
  endpointUp := fun _ _ _ _ _ _ => 1
  endpointUp_pos := fun _ _ _ _ _ _ => one_pos
  σcolUp := fun _ _ _ _ _ _ _ => 1
  σcolUp_pos := fun _ _ _ _ _ _ _ => one_pos
  I₁ := ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2
  I₁_pos := (by norm_num : (0 : ℝ) < 1 / 3).trans_le one_third_le_integral_sinh_sq
  scaleUp := fun _ ci ex _ => posOr_VAL3 (ci.γc / (1200000 * ex.Δ))
  scaleUp_pos := fun _ _ _ _ => posOr_pos_VAL3 _
  wUp := fun _ _ _ _ _ => 1
  wUp_pos := fun _ _ _ _ _ => one_pos
  splitUp := fun _ _ _ _ _ => 1
  splitUp_pos := fun _ _ _ _ _ => one_pos
  β₁Up := fun _ _ _ _ _ _ => 1
  β₁Up_pos := fun _ _ _ _ _ _ => one_pos
  T₀Low := fun _ _ _ _ _ _ _ => 0
  lpa02V := fun _ _ _ _ _ _ _ T₀ => T₀
  T₀_le_lpa02V := fun _ _ _ _ _ _ _ _ => le_rfl
  LmaxLow := fun _ _ _ _ _ _ => 0
  tailLow := fun _ _ _ _ _ _ _ => 0
  H := fun m => (m : ℝ)
  H_tendsto := tendsto_natCast_atTop_atTop

/-- **The scale budget at every register** (PR19 `scaleUp`, the C14 producer's conditions on `Λ`
verbatim) of every strategy below the scale strategy (FC39-VAL4's proof on register V3). -/
theorem closedScaleBudgetV3_of_below_VAL5 {D : ClosedEarlyData} {T : ClosedThresholdsV3 D}
    (hTU : ClosedStrategyBelowV3 T (scaleStrategyV3 D)) (R : ClosedRegisterV3 D T) :
    ClosedScaleBudgetV3 R := by
  have hΔ0 : 0 < R.later.excl.Δ := R.later.Δ_pos_VAL5
  have hγc0 : 0 < R.later.circle.γc := R.later.γc_pos
  have hτ0 : 0 < R.later.err.bd.τ := R.later.τ_pos
  have hεU := R.later.ε_lt.trans_le (hTU.errorsUp_le _ _ _)
  have hε : R.later.err.co.ε < R.later.circle.γc / 8000 :=
    hεU.trans_eq (posOr_eq_VAL3 (by positivity))
  have hroot : 504000 * (4000 / R.later.circle.γc) ^ 2 < R.later.excl.Δ :=
    ((hTU.ΔLow_ge _ _ _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt
      R.later.Δ_gt
  have hΛU := R.later.Λ_lt.trans_le (hTU.scaleUp_le _ _ _ _)
  have hΛ : R.later.scale.Λ < R.later.circle.γc / (1200000 * R.later.excl.Δ) :=
    hΛU.trans_eq (posOr_eq_VAL3 (by positivity))
  have hτU := (R.later.τ_lt.trans_le (min_le_right _ _)).trans_le (hTU.sectionUp_le _ _ _ _)
  have hτ : R.later.err.bd.τ < (R.later.circle.γc / 4000) ^ 2 / 3780 :=
    hτU.trans_eq (posOr_eq_VAL3 (by positivity))
  have hL := R.later.regScale_L
  unfold closedLongLength at hL
  have h2 := R.later.regScale_two
  have h100 := R.later.regScale_100
  refine ⟨by linarith only [h2], ?_, (h100.trans (by norm_num)).le,
    c14_staged_budget_FAM2b hγc0 hε hroot hΛ hτ0.le hτ,
    R.later.lfr29_Λ.trans_eq (by norm_num), h100.le⟩
  rw [lt_div_iff₀ (by positivity)]
  linarith only [hL]

/-! ### The rows strategy and the 15 rows -/

/-- **The rows strategy on register V3**: the infimum of the scale strategy, FC39-VAL4's 11-row
strategy and the circle rows strategy (`I₁ = ∫₀¹ sinh²` from the scale strategy). -/
def rowsStrategyV3 (D : ClosedEarlyData) : ClosedThresholdsV3 D :=
  ((scaleStrategyV3 D).inf (partialRowsStrategyV3 D)).inf (circleRowsStrategyV3 D)

/-- **All 15 chapter-14 rows at every register V3 of a strategy below the rows strategy**: with
`C_ge`, for every register `R` at `T`, every `εr < ε₀`, `20Λz ≤ T₀` and every final family at
`R`'s values, the conclusions of TCP01–TCP06, EGP03, EGP04, EGP06, EGP07, SGP01–SGP04, SGP06 at the
register's tolerances (in the order of `ClosedRowOutsV3`). -/
theorem rowOuts_of_below_VAL5 {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j)
    {T : ClosedThresholdsV3 D} (hTU : ClosedStrategyBelowV3 T (rowsStrategyV3 D))
    (R : ClosedRegisterV3 D T) {K : ℕ} {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {δ εr Λz : ℝ} (hεr : εr < R.later.err.co.ε₀)
    (hΛz : 20 * Λz ≤ R.later.split.T₀)
    (P : LocalChartPacketsC14 X g hmetric ρ hρ R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
      R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
      R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz) :
    Tcp01GramOutV2 P.toLocalChartPackets ∧
    Tcp02OutV2 P.toLocalChartPackets R.later.circle.E ∧
    Tcp03ZeroOutV2 P.toLocalChartPacketsZ R.later.circle.θ₂ ∧
    Tcp04OutV2 P.toLocalChartPackets R.later.circle.θ₂ ∧
    Tcp05OutV2 P (R.stage.e 0) ∧
    Tcp06OutV2 P (R.stage.Γ 0) (R.stage.Sig 0) (R.stage.e 0) ∧
    Egp03OutV2 P.toLocalChartFamilyE R.later.circle.E ∧
    Egp04OutV2 P.toLocalChartPacketsRVZ R.later.circle.θe ∧
    Egp06OutV2 P.toLocalChartPacketsRVZ (R.stage.e 1) ∧
    Egp07OutV2 P (R.stage.Γ 1) (R.stage.Sig 1) (R.stage.e 1) ∧
    Sgp01OutV2 P.toLocalChartPacketsR ∧
    Sgp02OutV2 P.toLocalChartFamilyQ R.later.circle.E ∧
    Sgp03ZeroOutV2 P.toLocalChartPacketsRVZ R.later.circle.θs
      (R.later.circle.θs ^ 2 / (2 * 10 ^ 6)) ∧
    Sgp04OutV2 P.toLocalChartPacketsRVZ (R.stage.e 2) ∧
    Sgp06OutV2 P (R.stage.Γ 2) (R.stage.Sig 2) (R.stage.e 2) := by
  have h11 : ClosedStrategyBelowV3 T (partialRowsStrategyV3 D) :=
    hTU.trans_VAL5 ((ClosedThresholdsV3.inf_below_left_VAL5 _ _).trans_VAL5
      (ClosedThresholdsV3.inf_below_right_VAL5 _ _))
  have h4 : ClosedStrategyBelowV3 T (circleRowsStrategyV3 D) :=
    hTU.trans_VAL5 (ClosedThresholdsV3.inf_below_right_VAL5 _ _)
  obtain ⟨t1, t2, e3, e4, e6, e7, s1, s2, s3, s4, s6⟩ :=
    partialRowOuts_of_below_VAL5 hC h11 R hεr hΛz P
  obtain ⟨t3, t4, t5, t6⟩ := circleRowOuts_of_below_VAL5 hC h4 R hεr hΛz P
  exact ⟨t1, t2, t3, t4, t5, t6, e3, e4, e6, e7, s1, s2, s3, s4, s6⟩

/-- **The `rows` field**: every instance of the final family at a register V3 of a strategy below
the rows strategy carries `ClosedRowOutsV3`. -/
theorem closedRowOuts_of_below_VAL5 {K : ℕ} {D : ClosedEarlyData}
    (hC : ∀ j, gafGraphConst j ≤ D.C j) {T : ClosedThresholdsV3 D}
    (hTU : ClosedStrategyBelowV3 T (rowsStrategyV3 D)) {R : ClosedRegisterV3 D T}
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g}
    {δ εr Λz : ℝ} (F : ClosedFamilyInstanceV3 K R M δ εr Λz) (hεr : εr < R.later.err.co.ε₀)
    (hΛz : 20 * Λz ≤ R.later.split.T₀) : ClosedRowOutsV3 F := by
  unfold ClosedRowOutsV3
  exact rowOuts_of_below_VAL5 hC hTU R hεr hΛz F.family

/-! ### Realization with the rows and the inhabited partial record -/

/-- **The complete realization with the scale budget and all 15 rows** (review 52, order of work
steps 3–4): with `C_ge`, ONE common strategy `T` (refining the rows strategy) with `H m = m + 2`
and `lc18 ≤` LC18's obstruction, at which every register V3 is realized on its tail by the
complete instance (`ClosedFamilyAtV3`: final family `LocalChartPacketsC14` at the register's
values from `LocalChartPacketsC14D`, LPA02's joint witness, zero-ball selection, LC09, LC18), every
register meets the producer's scale conditions, and every instance carries `ClosedRowOutsV3`. -/
theorem exists_closed_realization_rows_VAL5 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j) :
    ∃ T : ClosedThresholdsV3 D, ClosedStrategyRefinesV3 T (rowsStrategyV3 D) ∧
      (∀ m, T.H m = (m : ℝ) + 2) ∧ T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      ClosedFamilyAtV3 K Wseq gseq T ∧ (∀ R : ClosedRegisterV3 D T, ClosedScaleBudgetV3 R) ∧
      ∀ (R : ClosedRegisterV3 D T) (δ εr Λz : ℝ), εr < R.later.err.co.ε₀ →
        20 * Λz ≤ R.later.split.T₀ → ∀ m (M : ClosedModel (Wseq m) (gseq m))
        (F : ClosedFamilyInstanceV3 K R M δ εr Λz), ClosedRowOutsV3 F := by
  obtain ⟨T, hTU, hH, hlc, hfam⟩ :=
    exists_closed_realization_VAL5 K hK A hA Wseq gseq hf hg (rowsStrategyV3 D)
  have hb := hTU.below_VAL5
  have hsc : ClosedStrategyBelowV3 T (scaleStrategyV3 D) :=
    hb.trans_VAL5 ((ClosedThresholdsV3.inf_below_left_VAL5 _ _).trans_VAL5
      (ClosedThresholdsV3.inf_below_left_VAL5 _ _))
  exact ⟨T, hTU, hH, hlc, hfam, closedScaleBudgetV3_of_below_VAL5 hsc,
    fun _ _ _ _ hεr hΛz _ _ F => closedRowOuts_of_below_VAL5 hC hb F hεr hΛz⟩

/-- **The partial closed validity on register V3 holds** (review 52; record
`PartialClosedThresholdValidityV3Rows`): at the early data `closedEarlyDataShared K` (constant
provenance, the ONE shared CFS15 modulus), on every closed standing sequence of members, there is a
strategy `T` at which EVERY field holds: the early constants (`N, P, L₀, Ξ_cfs15, Ξ_range, C`),
LC18's obstruction, `I₁ = ∫₀¹ sinh²`, LPA01's standing clauses at `H m = m + 2`, the complete
family package at every register (LPA02's joint witness and selection included), the scale budget
and all 15 chapter-14 rows. -/
theorem exists_partialClosedThresholdValidityV3Rows_VAL5 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV3 (closedEarlyDataShared K),
      PartialClosedThresholdValidityV3Rows K A Wseq gseq (closedEarlyDataShared K) T := by
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := closedEarlyDataShared_fields_VAL5 K
  obtain ⟨T, hTU, hH, hlc, hfam, hsc, hrows⟩ :=
    exists_closed_realization_rows_VAL5 K hK A hA Wseq gseq hf hg hC
  refine ⟨T, ⟨⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hlc, hTU.I₁_eq, fun m p => ?_, fun _ => hfam⟩,
    hC, hsc, fun R δ εr Λz hεr hΛz m M F => hrows R δ εr Λz hεr hΛz m M F⟩⟩
  rw [hH m]
  exact closed_standing_clauses_VAL K A Wseq gseq hg m p

end DifferentialGeometry.Geometry.Collapse
