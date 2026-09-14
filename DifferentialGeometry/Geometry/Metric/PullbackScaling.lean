import DifferentialGeometry.Geometry.Metric.Pullback.Cross
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

theorem Diffeomorph.inner_sqrt_smul_mfderiv [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (c : Real) (hc : 0 < c) (x : M) (v w : TangentSpace I x) :
    g.inner (Φ x) (Real.sqrt c • mfderiv I J Φ x v)
      (Real.sqrt c • mfderiv I J Φ x w) =
        (Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ).inner x v w := by
  rw [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, Real.mul_self_sqrt hc.le]

end DifferentialGeometry
