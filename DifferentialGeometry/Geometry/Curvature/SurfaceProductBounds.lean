import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Metric.Product.Completeness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N]

theorem normSq0S_metricRm04At_le_of_pullbackMetricCross_eq_prod_real
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (N × ℝ) M ∞)
    (hprod : Diffeomorph.pullbackMetricCross g Φ = h.prod (euclideanMetric (E := ℝ)))
    {B : ℝ} (hB : ∀ x : M, normSq0S g x 4 (metricRm04At g x) ≤ B) :
    ∀ y : N, normSq0S h y 4 (metricRm04At h y) ≤ B := by
  intro y
  have hp := CheegerGromovCompactness.riemannNormSq_cross g Φ (y, 0)
  rw [hprod, normSq0S_metricRm04At_productReal] at hp
  exact hp.le.trans (hB (Φ (y, 0)))

theorem complete_and_curvature_bound_of_pullbackMetricCross_eq_prod_real
    [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (N × ℝ) M ∞)
    (hprod : Diffeomorph.pullbackMetricCross g Φ = h.prod (euclideanMetric (E := ℝ)))
    (hg : RiemannianMetricComplete g)
    {B : ℝ} (hB : ∀ x : M, normSq0S g x 4 (metricRm04At g x) ≤ B) :
    RiemannianMetricComplete h ∧ ∀ y : N, normSq0S h y 4 (metricRm04At h y) ≤ B := by
  refine ⟨?_, normSq0S_metricRm04At_le_of_pullbackMetricCross_eq_prod_real g h Φ hprod hB⟩
  have hc := RiemannianMetricComplete.pullbackCross g Φ hg
  rw [hprod] at hc
  exact RiemannianMetricComplete.fst_of_prod hc 0

end DifferentialGeometry.Geometry.Curvature
