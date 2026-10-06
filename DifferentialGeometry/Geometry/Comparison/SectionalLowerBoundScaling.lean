import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- Multiplying a metric by a positive constant divides its sectional lower
bound by that constant. -/
theorem SectionalBoundedBelowAt.scaleMetric
    {g : SmoothRiemannianMetric I M} {Ksec : ℝ} {x : M}
    (hsec : SectionalBoundedBelowAt g x Ksec) (c : ℝ) (hc : 0 < c) :
    SectionalBoundedBelowAt (scaleMetric c hc g) x (Ksec / c) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  intro v w
  have h := hsec v w
  simp only [scaleMetric_inner, metricRmStandard_scale (I := I) c hc g x v w w v]
  have hLHS :
      Ksec / c * (c * g.inner x v v * (c * g.inner x w w) - (c * g.inner x v w) ^ 2) =
        c * (Ksec * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) := by
    field_simp [hc.ne']
  rw [hLHS]
  exact mul_le_mul_of_nonneg_left h hc.le

end DifferentialGeometry.Geometry.Riemannian
