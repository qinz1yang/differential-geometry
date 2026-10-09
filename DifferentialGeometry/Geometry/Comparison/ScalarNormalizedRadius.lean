import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem scale_bounds_of_scalar_bounds_of_local_pullback
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M → N) (hΦ : IsLocalDiffeomorph I J ∞ Φ) {q C : ℝ} (hq : 0 < q)
    (hmetric : g = localPullMetric (scaleMetric q hq h) Φ hΦ) (u : M)
    (hlower : 1 / 2 < metricScalarAt g u) (hupper : metricScalarAt g u < C) :
    0 < metricScalarAt h (Φ u) ∧
      metricScalarAt h (Φ u) / C < q ∧ q < 2 * metricScalarAt h (Φ u) := by
  have hscalar : metricScalarAt g u = metricScalarAt h (Φ u) / q := by
    rw [hmetric, metricScalarAt_localPull, metricScalarAt_scaleMetric]
    ring
  have hC : 0 < C := by linarith
  rw [hscalar] at hlower hupper
  have hlo := (lt_div_iff₀ hq).mp hlower
  have hup := (div_lt_iff₀ hq).mp hupper
  refine ⟨by linarith, (div_lt_iff₀ hC).mpr ?_, ?_⟩
  · nlinarith
  · linarith

end DifferentialGeometry.Geometry.Curvature



namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem scalar_normalized_image_ball_of_local_pullback
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M → N) (hΦ : IsLocalDiffeomorph I J ∞ Φ) {q C R : ℝ}
    (hq : 0 < q) (hR : 0 < R)
    (hmetric : ∀ x (v w : TangentSpace I x),
      g.inner x v w = q * h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (tip u : M) (K : Set M)
    (hlower : 1 / 2 < metricScalarAt g u) (hupper : metricScalarAt g u < C)
    (hpoint : riemannianEDistOf (scaleMetric q hq h) (Φ tip) (Φ u) ≤ ENNReal.ofReal (2 * R))
    (hK : ∀ x ∈ K,
      riemannianEDistOf (scaleMetric q hq h) (Φ tip) (Φ x) ≤ ENNReal.ofReal (2 * R)) :
    ∃ hS : 0 < metricScalarAt h (Φ u),
      metricScalarAt h (Φ u) / C < q ∧ q < 2 * metricScalarAt h (Φ u) ∧
      Φ '' K ⊆ riemannianBallOf (scaleMetric (metricScalarAt h (Φ u)) hS h) (Φ u)
        (4 * R * Real.sqrt C) := by
  have heq : g = localPullMetric (scaleMetric q hq h) Φ hΦ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, scaleMetric_inner]
    exact hmetric x v w
  obtain ⟨hS, hscale, htwo⟩ := scale_bounds_of_scalar_bounds_of_local_pullback
    g h Φ hΦ hq heq u hlower hupper
  refine ⟨hS, hscale, htwo, ?_⟩
  have hratio : metricScalarAt h (Φ u) / q < C := by
    have hscalar : metricScalarAt g u = metricScalarAt h (Φ u) / q := by
      rw [heq, metricScalarAt_localPull, metricScalarAt_scaleMetric]
      ring
    rwa [hscalar] at hupper
  apply Geometry.Metric.subset_ball_of_scaled_tip_distance_bounds h (Φ tip) (Φ u) (Φ '' K)
    hq hS hR hratio hpoint
  rintro _ ⟨x, hx, rfl⟩
  exact hK x hx

end DifferentialGeometry.Geometry.Curvature
