import DifferentialGeometry.Geometry.Metric.ChartLipschitz.Intrinsic
import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open scoped ContDiff ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm
    [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p α : M) {R : ℝ} (hR : 0 < R) :
    LocallyLipschitzOn (extChartAt I α).target
      (radialDistanceCutoff g p R ∘ (extChartAt I α).symm) := by
  let L : ℝ≥0 := ⟨1 / R, by positivity⟩
  apply locallyLipschitzOn_comp_extChartAt_symm_of_edist_le g α (L := L)
  intro x y
  have hL : ENNReal.ofReal (1 / R) = (L : ℝ≥0∞) := by
    change ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  simpa only [hL] using edist_radialDistanceCutoff_le g p hR x y

end DifferentialGeometry.Geometry.Riemannian

end
