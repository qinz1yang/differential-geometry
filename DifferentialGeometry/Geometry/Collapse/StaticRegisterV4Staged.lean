import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Edp06

/-!
# The inhabited partial record on register V4 with the staged collar requests (lane FC39-VAL6)

The record of `StaticRegisterV4NbCw` (`exists_partialClosedThresholdValidityV4Rows_nbcw_VAL6`) on
the rows strategy capped by TCP04's request `β₂ < γc/1000` (`ClosedThresholdsV4.withCollarβ₂_VAL6`,
`StaticRegisterV4Edp06`). At every register of the resulting strategy the stage-2/3 requests of the
staged contract `C14StagedRequestsSTG` that read only register values hold together: `βc < γc/1000`,
`3βc ≤ β 2` (EDP06's collar request) and `β₂ < γc/1000` (TCP04, B:5483), with `β 3 ≤` LC18's
threshold; EDP06's step on every register's tail follows from the record by
`PartialClosedThresholdValidityV4.edp06_on_tail_VAL6`.

* `ClosedThresholdsV4.withCollarβ₂_below_VAL6`: the cap is below the uncapped strategy.
* `exists_partialClosedThresholdValidityV4Rows_staged_VAL6`: the consumer.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The cap by TCP04's `β₂ < γc/1000` only lowers `β₂`'s slot. -/
theorem ClosedThresholdsV4.withCollarβ₂_below_VAL6 {D : ClosedEarlyData}
    (U : ClosedThresholdsV4 D) : ClosedStrategyBelowV4 U.withCollarβ₂_VAL6 U where
  lc18_le := le_rfl
  circleUp_le := fun _ _ _ _ _ => le_rfl
  β₂Up_le := fun _ _ _ => min_le_left _ _
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => le_rfl
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  endpointUp_le := fun _ _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => le_rfl
  β₁Up_le := fun _ _ _ _ _ _ => le_rfl
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl
  LmaxLow_ge := fun _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- **The partial closed validity on register V4 with the staged collar requests**: at the early
data `earlyDataSharedV4 K`, on every closed standing sequence, one strategy `T` at which the whole
record `PartialClosedThresholdValidityV4Rows` holds, the `N_b, c_w` slots are PR10's values, and at
EVERY register `βc < γc/1000`, `3βc ≤ β 2`, `β₂ < γc/1000` (TCP04) and `β 3 ≤` LC18's threshold. -/
theorem exists_partialClosedThresholdValidityV4Rows_staged_VAL6 (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = sharedNb_VAL6 ∧ T.cw = sharedCw_VAL6 ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        R.later.circle.βc < R.later.circle.γc / 1000 ∧ 3 * R.later.circle.βc ≤ R.β 2 ∧
        R.later.excl.β₂ < R.later.circle.γc / 1000 ∧
        R.β 3 ≤ threeSplittingExclusionThreshold.{0, 0} := by
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := earlyDataSharedV4_fields_VAL6 K
  obtain ⟨T, hTU, hH, hlc, hfam⟩ :=
    exists_closed_realization_VAL6 K hK A hA Wseq gseq hf hg
      (rowsStrategyNbV4 (earlyDataSharedV4 K)).withCollarβ₂_VAL6
  have hcap : ClosedStrategyBelowV4 T (rowsStrategyNbV4 (earlyDataSharedV4 K)).withCollarβ₂_VAL6 :=
    hTU.below_VAL6
  have hb : ClosedStrategyBelowV4 T (rowsStrategyV4 (earlyDataSharedV4 K)) :=
    (hcap.trans_VAL6 (ClosedThresholdsV4.withCollarβ₂_below_VAL6 _)).trans_VAL6
      (rowsStrategyNbV4_below_VAL6 _)
  have hsc : ClosedStrategyBelowV4 T (scaleStrategyV4 (earlyDataSharedV4 K)) :=
    hb.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
      (ClosedThresholdsV4.inf_below_left_VAL6 _ _))
  refine ⟨T, ⟨⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hlc, hTU.I₁_eq, fun m p => ?_, fun _ => hfam⟩,
    hC, closedScaleBudgetV4_of_below_VAL6 hsc,
    fun _ _ _ _ hεr hΛz _ _ F => closedRowOuts_of_below_VAL6 hC hb F hεr hΛz⟩,
    hTU.Nb_eq, hTU.cw_eq, fun R => ⟨R.later.βc_lt_γc_VAL6, R.three_mul_βc_le_β_two_VAL6,
    R.β₂_lt_γc_of_below_VAL6 hcap, ?_⟩⟩
  · rw [hH m]
    exact closed_standing_clauses_VAL K A Wseq gseq hg m p
  · rw [R.β_three_VAL6]
    exact (R.later.β₃_lt.trans_le hlc).le

end DifferentialGeometry.Geometry.Collapse
