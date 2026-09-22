import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross

section
set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem pullback_metric_inner_eq_sub_two_mul_ricci
    (g : ℝ → SmoothRiemannianMetric J N)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : N, ∀ v w : TangentSpace J x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w)
    (d : M ≃ₘ⟮I, J⟯ N) (h : SmoothRiemannianMetric I M)
    (hd : Diffeomorph.pullbackMetricCross (g 0) d = h)
    (t : ℝ) (ht : t ≤ 0) (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetricCross (g t) d).inner x v w =
      h.inner x v w - 2 * t * ricciTensor h x v w := by
  rw [Diffeomorph.pullbackMetricCross_inner, hflow t ht]
  rw [← Diffeomorph.pullbackMetricCross_inner (g 0) d,
    ← ricciTensor_pullbackCross (g 0) d, hd]

end DifferentialGeometry.Geometry.Curvature

end

end
