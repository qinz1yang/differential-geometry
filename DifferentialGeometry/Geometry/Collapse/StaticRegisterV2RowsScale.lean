import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2RowsStrategy

/-!
# The scale budget at every register of the common strategy (lane FC39-VAL4; PARTIAL record)

`PartialClosedThresholdValidityV2Rows.scale_budget` asks for `ClosedScaleBudgetV2 R` (the C14
producer's conditions on `Λ`, verbatim) at EVERY staged register. Four of the six follow from the
register alone; the `γc`-budget `2ε + 300ΔΛ + √(504000/Δ + 3780τ) < γc/1000` needs the requests
`ε < γc/8000`, `Δ > 504000(4000/γc)²`, `Λ < γc/(1200000Δ)` and `τ < (γc/4000)²/3780`, which are
added here to the rows strategy (FC39-VAL4 G2).

* `partialRowsScaleStrategyV2 D`: `partialRowsStrategyV2 D` with those four requests added to
  `errorsUp`, `ΔLow`, `scaleUp`, `sectionUp`; `ClosedStrategyRefinesV2.rows_VAL4` (a strategy
  refining it refines the rows strategy).
* `closedScaleBudgetV2_of_refines_VAL4`: `ClosedScaleBudgetV2 R` at every register of every
  strategy refining it.
* Consumer `exists_closed_realization_rows_scale_C14D_VAL4`: ONE common strategy with the C14D
  realization (G1), the scale budget at every register and the 11 row conclusions (G2) on every
  instance.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **The rows strategy with the producer's `γc`-budget requests** (`ε < γc/8000`,
`Δ > 504000(4000/γc)²`, `Λ < γc/(1200000Δ)`, `τ < (γc/4000)²/3780`). -/
def partialRowsScaleStrategyV2 (D : ClosedEarlyData) : ClosedThresholdsV2 D :=
  { partialRowsStrategyV2 D with
    ΔLow := fun _ ci _ _ => 504000 * (4000 / ci.γc) ^ 2
    errorsUp := fun st ci ex => min ((partialRowsStrategyV2 D).errorsUp st ci ex)
      (posOr_VAL3 (ci.γc / 8000))
    errorsUp_pos := fun st ci ex =>
      lt_min ((partialRowsStrategyV2 D).errorsUp_pos st ci ex) (posOr_pos_VAL3 _)
    sectionUp := fun st ci ex co => min ((partialRowsStrategyV2 D).sectionUp st ci ex co)
      (posOr_VAL3 ((ci.γc / 4000) ^ 2 / 3780))
    sectionUp_pos := fun st ci ex co =>
      lt_min ((partialRowsStrategyV2 D).sectionUp_pos st ci ex co) (posOr_pos_VAL3 _)
    scaleUp := fun _ ci ex _ => min 1 (posOr_VAL3 (ci.γc / (1200000 * ex.Δ)))
    scaleUp_pos := fun _ _ _ _ => lt_min one_pos (posOr_pos_VAL3 _) }

/-- A strategy refining the scale strategy refines the rows strategy. -/
theorem ClosedStrategyRefinesV2.rows_VAL4 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (h : ClosedStrategyRefinesV2 T (partialRowsScaleStrategyV2 D)) :
    ClosedStrategyRefinesV2 T (partialRowsStrategyV2 D) where
  Nb_eq := h.Nb_eq
  cw_eq := h.cw_eq
  I₁_eq := h.I₁_eq
  LmaxLow_eq := h.LmaxLow_eq
  endpointUp_eq := h.endpointUp_eq
  circleUp_le := h.circleUp_le
  lc18_le := h.lc18_le
  β₂Up_le := h.β₂Up_le
  ΔLow_ge := fun st ci β₃ β₂ =>
    (mul_nonneg (by norm_num) (sq_nonneg (4000 / ci.γc))).trans (h.ΔLow_ge st ci β₃ β₂)
  errorsUp_le := fun st ci ex => (h.errorsUp_le st ci ex).trans (min_le_left _ _)
  sectionUp_le := fun st ci ex co => (h.sectionUp_le st ci ex co).trans (min_le_left _ _)
  lfr29W_le := h.lfr29W_le
  σcolUp_le := h.σcolUp_le
  scaleUp_le := fun st ci ex er => (h.scaleUp_le st ci ex er).trans (min_le_left _ _)
  wUp_le := h.wUp_le
  splitUp_le := h.splitUp_le
  β₁Up_le := h.β₁Up_le
  T₀Low_ge := h.T₀Low_ge
  tailLow_ge := h.tailLow_ge

/-- **The scale budget at every register** (PR19 `scaleUp`, the C14 producer's conditions on `Λ`
verbatim) of every strategy refining the scale strategy. -/
theorem closedScaleBudgetV2_of_refines_VAL4 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (hTU : ClosedStrategyRefinesV2 T (partialRowsScaleStrategyV2 D)) (R : ClosedRegisterV2 D T) :
    ClosedScaleBudgetV2 R := by
  have hΔ0 : 0 < R.later.excl.Δ := R.later.Δ_pos_VAL2
  have hγc0 : 0 < R.later.circle.γc := R.later.γc_pos
  have hτ0 : 0 < R.later.err.bd.τ := R.later.τ_pos
  have hεU := R.later.ε_lt.trans_le ((hTU.errorsUp_le _ _ _).trans (min_le_right _ _))
  have hε : R.later.err.co.ε < R.later.circle.γc / 8000 :=
    hεU.trans_eq (posOr_eq_VAL3 (by positivity))
  have hroot : 504000 * (4000 / R.later.circle.γc) ^ 2 < R.later.excl.Δ :=
    ((hTU.ΔLow_ge _ _ _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt
      R.later.Δ_gt
  have hΛU := R.later.Λ_lt.trans_le ((hTU.scaleUp_le _ _ _ _).trans (min_le_right _ _))
  have hΛ : R.later.scale.Λ < R.later.circle.γc / (1200000 * R.later.excl.Δ) :=
    hΛU.trans_eq (posOr_eq_VAL3 (by positivity))
  have hτU := (R.later.τ_lt.trans_le (min_le_right _ _)).trans_le
    ((hTU.sectionUp_le _ _ _ _).trans (min_le_right _ _))
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

/-- **The realization with the scale budget and the 11 rows on `LocalChartPacketsC14D`** (review
52, PARTIAL record): with `C_ge`, ONE common strategy at which every staged register is realized on
its tail by `LocalChartPacketsC14D`, meets the producer's scale conditions (`scale_budget`), and
every instance at every register carries the 11 row conclusions of FC39-VAL4 G2. -/
theorem exists_closed_realization_rows_scale_C14D_VAL4 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j) :
    ∃ T : ClosedThresholdsV2 D, (∀ m, T.H m = (m : ℝ) + 2) ∧
      T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      PartialClosedFamilyAtC14DV2 K Wseq gseq T ∧
      (∀ R : ClosedRegisterV2 D T, ClosedScaleBudgetV2 R) ∧
      ∀ (R : ClosedRegisterV2 D T) (δ εr Λz : ℝ), εr < R.later.err.co.ε₀ →
        20 * Λz ≤ R.later.split.T₀ → ∀ m (M : ClosedModel (Wseq m) (gseq m))
        (F : PartialClosedFamilyInstanceC14DV2 K R M δ εr Λz),
        PartialClosedRowOutsV2 R F.family.toLocalChartPacketsC14 := by
  obtain ⟨T, hTU, hH, hlc, hfam⟩ :=
    exists_closed_realization_C14D_VAL4 K hK A hA Wseq gseq hf hg (partialRowsScaleStrategyV2 D)
  exact ⟨T, hH, hlc, hfam, closedScaleBudgetV2_of_refines_VAL4 hTU, fun R _ _ _ hεr hΛz _ _ F =>
    partialRowOuts_of_refines_VAL4 hC hTU.rows_VAL4 R hεr hΛz F.family.toLocalChartPacketsC14⟩

end DifferentialGeometry.Geometry.Collapse
