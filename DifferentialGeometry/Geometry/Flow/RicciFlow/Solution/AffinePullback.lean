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

theorem metric_inner_eq_affine_ricci_of_pullback
    (g : ℝ → SmoothRiemannianMetric J N) (d : M ≃ₘ⟮I, J⟯ N)
    {A : Set ℝ} {b : ℝ}
    (hflow : ∀ t ∈ A, ∀ x : M, ∀ v w : TangentSpace I x,
      (Diffeomorph.pullbackMetricCross (g t) d).inner x v w =
        (Diffeomorph.pullbackMetricCross (g b) d).inner x v w +
          2 * (b - t) * ricciTensor (Diffeomorph.pullbackMetricCross (g b) d) x v w) :
    ∀ t ∈ A, ∀ x : N, ∀ v w : TangentSpace J x,
      (g t).inner x v w =
        (g b).inner x v w + 2 * (b - t) * ricciTensor (g b) x v w := by
  have hdouble (t : ℝ) :
      Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross (g t) d) d.symm = g t :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mp rfl
  intro t ht x v w
  calc
    (g t).inner x v w =
        (Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross (g t) d) d.symm).inner
          x v w := by rw [hdouble]
    _ = (g b).inner x v w + 2 * (b - t) * ricciTensor (g b) x v w := by
      rw [Diffeomorph.pullbackMetricCross_inner, hflow t ht,
        ← Diffeomorph.pullbackMetricCross_inner (Diffeomorph.pullbackMetricCross (g b) d) d.symm,
        ← ricciTensor_pullbackCross (Diffeomorph.pullbackMetricCross (g b) d) d.symm,
        hdouble]

end DifferentialGeometry.Geometry.Curvature
