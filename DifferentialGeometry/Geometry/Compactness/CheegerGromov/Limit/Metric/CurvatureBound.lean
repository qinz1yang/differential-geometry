import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g r : SmoothRiemannianMetric I M)
    (x : M) (hconv : MetricCPConvergenceOn {x} 2 gSeq g r) (hdim : Module.finrank ℝ E = 3)
    (hnonneg : metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I)) {C : ℝ}
    (hbound : ∀ᶠ i in atTop, normSq0S (gSeq i) x 4 (metricRm04At (gSeq i) x) ≤ C) :
    normSq0S g x 4 (metricRm04At g x) ≤ 100 ^ 2 * (9 * Real.sqrt C) ^ 2 := by
  have hscal :=
    (hconv.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at (mem_singleton x)
  have hscalar : |metricScalarAt g x| ≤ 9 * Real.sqrt C := by
    apply le_of_tendsto hscal.abs
    filter_upwards [hbound] with i hi
    have hh := (scalar_abs_le_rm (gSeq i) x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (sq_nonneg _))
    change |metricScalarAt (gSeq i) x| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C at hh
    simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  have hR := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative g x hdim hnonneg
  have hsq : (metricScalarAt g x) ^ 2 ≤ (9 * Real.sqrt C) ^ 2 := by
    have hB : 0 ≤ 9 * Real.sqrt C := by positivity
    nlinarith [sq_abs (metricScalarAt g x), abs_nonneg (metricScalarAt g x)]
  exact hR.trans (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))

end DifferentialGeometry.CheegerGromovCompactness
