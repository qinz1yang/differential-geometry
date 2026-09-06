import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem Diffeomorph.pullbackMetricCross_scaleMetric
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (c : Real) (hc : 0 < c) :
    Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ =
      scaleMetric c hc (Diffeomorph.pullbackMetricCross g Φ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner]

end DifferentialGeometry
