import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2RowsScale

/-!
# The rows-and-scale realization at the constant early data (lane FC39-VAL4; PARTIAL record)

`closedEarlyDataV3 K` (FC39-VAL3 G3a: the early constants of the actual producers,
`C = gafGraphConst`) meets `C_ge` with equality, so FC39-VAL4 G3's realization needs nothing
beyond the members' data:

* `exists_closed_realization_rows_scale_early_VAL4`: at the early data `closedEarlyDataV3 K`, ONE
  common strategy at which every staged register is realized on its tail by
  `LocalChartPacketsC14D`, meets the producer's scale conditions, and every instance carries the 11
  row conclusions of FC39-VAL4 G2 (TCP03–TCP06 obstructed, see `StaticRegisterV2RowsStrategy`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **The rows-and-scale realization at the constant early data** (PARTIAL record: 11 of 15 rows,
no LPA02 joint witness export). -/
theorem exists_closed_realization_rows_scale_early_VAL4 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV2 (closedEarlyDataV3 K), (∀ m, T.H m = (m : ℝ) + 2) ∧
      T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      PartialClosedFamilyAtC14DV2 K Wseq gseq T ∧
      (∀ R : ClosedRegisterV2 (closedEarlyDataV3 K) T, ClosedScaleBudgetV2 R) ∧
      ∀ (R : ClosedRegisterV2 (closedEarlyDataV3 K) T) (δ εr Λz : ℝ), εr < R.later.err.co.ε₀ →
        20 * Λz ≤ R.later.split.T₀ → ∀ m (M : ClosedModel (Wseq m) (gseq m))
        (F : PartialClosedFamilyInstanceC14DV2 K R M δ εr Λz),
        PartialClosedRowOutsV2 R F.family.toLocalChartPacketsC14 :=
  exists_closed_realization_rows_scale_C14D_VAL4 K hK A hA Wseq gseq hf hg
    (closedEarlyDataV3_fields_VAL3 K).2.2.2.2.2.2.2

end DifferentialGeometry.Geometry.Collapse
