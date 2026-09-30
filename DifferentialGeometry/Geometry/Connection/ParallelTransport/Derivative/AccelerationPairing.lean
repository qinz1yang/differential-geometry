import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.NormComparison
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem abs_covDerivAlong_velocity_pairing_div_le_of_reference_acceleration
    (g h : SmoothRiemannianMetric I M) (beta : ℝ → M) (t : ℝ)
    (hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta t)
    {Λ A B D U b : ℝ} (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hb : 0 < b)
    (hmetric : ∀ z : TangentSpace I (beta t),
      h.inner (beta t) z z ≤ Λ * g.inner (beta t) z z)
    (hconnection : ∀ u w : TangentSpace I (beta t),
      Real.sqrt (g.inner (beta t)
        (CovariantDerivative.difference (metricCov h) (metricCov g)
          (beta t) u w)
        (CovariantDerivative.difference (metricCov h) (metricCov g)
          (beta t) u w)) ≤
        A * Real.sqrt (g.inner (beta t) u u) * Real.sqrt (g.inner (beta t) w w))
    (hvelocity : Real.sqrt (g.inner (beta t)
      (mfderiv 𝓘(ℝ, ℝ) I beta t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I beta t (1 : ℝ))) ≤ B)
    (hacceleration : Real.sqrt (g.inner (beta t)
      (covDerivAlong g beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)
      (covDerivAlong g beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)) ≤ D)
    (w : TangentSpace I (beta t)) (hw : Real.sqrt (h.inner (beta t) w w) ≤ U) :
    |h.inner (beta t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t) w / (2 * b)| ≤
      (Real.sqrt Λ * (D + A * B ^ 2) * U) / (2 * b) := by
  have hbound := covDerivAlong_norm_le_of_connection_bound g h beta
    (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t hbeta hΛ hA
    hmetric hconnection hvelocity hvelocity hacceleration
  have hpair := DifferentialGeometry.SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
    h (beta t) (covDerivAlong h beta
      (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t) w
  have hD : 0 ≤ D := (Real.sqrt_nonneg _).trans hacceleration
  have hboundSq : Real.sqrt (h.inner (beta t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)) ≤
      Real.sqrt Λ * (D + A * B ^ 2) := by
    simpa only [pow_two, mul_assoc] using hbound
  have hprod : Real.sqrt (h.inner (beta t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)) *
      Real.sqrt (h.inner (beta t) w w) ≤
      (Real.sqrt Λ * (D + A * B ^ 2)) * U := by
    exact mul_le_mul hboundSq hw (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hD (mul_nonneg hA (sq_nonneg B))))
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hb)]
  apply div_le_div_of_nonneg_right _ (mul_pos (by norm_num) hb).le
  exact hpair.trans hprod

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
