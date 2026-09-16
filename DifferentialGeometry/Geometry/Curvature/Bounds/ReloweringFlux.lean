import DifferentialGeometry.Geometry.Curvature.Bounds.MixedMetricDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.ReloweringDifferenceNorm

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem norm_sq_cross_curvature_relowering_flux_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {C : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧ g₂.inner x v v ≤ C * g₁.inner x v v) :
    normSq0S (I := I) g₁ x 5
        (reLower (I := I) g₂ g₁
          (metricNabla0S (I := I) g₁
            (CovariantDerivative.rm04Section (I := I) g₁ (metricCov (I := I) g₂)
              (metricCov_smooth (I := I) g₂))) x -
          metricNabla0S (I := I) g₁
            (CovariantDerivative.rm04Section (I := I) g₁ (metricCov (I := I) g₂)
              (metricCov_smooth (I := I) g₂)) x) ≤
      (4 * (Module.finrank ℝ E : ℝ) ^ 15 * C ^ 7 *
          normSq0S (I := I) g₂ x 5
            (metricNabla0S (I := I) g₂
              (CovariantDerivative.rm04Section (I := I) g₂ (metricCov (I := I) g₂)
                (metricCov_smooth (I := I) g₂)) x) +
        (16 * (Module.finrank ℝ E : ℝ) ^ 18 * C ^ 8 +
          32 * (Module.finrank ℝ E : ℝ) ^ 19 * C ^ 6) *
            connectionDifferenceSq (I := I) g₁ g₂ x *
              normSq0S (I := I) g₂ x 4 (metricRm04At (I := I) g₂ x)) *
        metricDiffSq (I := I) g₁ g₂ x := by
  have hh : 0 ≤ metricDiffSq (I := I) g₁ g₂ x := by
    rw [metricDiffSq_def]
    exact normSq0S_nonneg (I := I) g₁ x 2 _
  have hn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 7 := by positivity
  have hdef := reLowerDefSq_le (I := I) (s := 4) g₁ g₂
    (metricNabla0S (I := I) g₁
      (CovariantDerivative.rm04Section (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂))) x
  have hderiv := norm_sq_covariant_derivative_cross_curvature_le (I := I) g₁ g₂ x hC heq
  refine hdef.trans ?_
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hderiv hh) hn
  convert h using 1
  ring

end DifferentialGeometry.Geometry.Curvature
