import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeDifference
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem covDerivAlong_norm_le_of_metric_comparison
    (g h : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (Y : ∀ t, TangentSpace I (gamma t)) (t : ℝ)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t)
    {Lambda : ℝ} (hLambda : 0 ≤ Lambda)
    (hmetric : ∀ z : TangentSpace I (gamma t),
      h.inner (gamma t) z z ≤ Lambda * g.inner (gamma t) z z) :
    Real.sqrt (h.inner (gamma t)
      (covDerivAlong h gamma Y t) (covDerivAlong h gamma Y t)) ≤
      Real.sqrt Lambda *
        (Real.sqrt (g.inner (gamma t)
          (covDerivAlong g gamma Y t) (covDerivAlong g gamma Y t)) +
        Real.sqrt (g.inner (gamma t)
          (CovariantDerivative.difference (metricCov h) (metricCov g) (gamma t)
            (Y t) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)))
          (CovariantDerivative.difference (metricCov h) (metricCov g) (gamma t)
            (Y t) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))))) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A : TangentSpace I (gamma t) :=
    CovariantDerivative.difference (metricCov h) (metricCov g) (gamma t)
      (Y t) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
  have hdecomp : covDerivAlong h gamma Y t = covDerivAlong g gamma Y t + A := by
    have hd := covAlong_diff h g gamma Y t hgamma
    change covDerivAlong h gamma Y t - covDerivAlong g gamma Y t = A at hd
    exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)
  calc
    _ ≤ Real.sqrt (Lambda * g.inner (gamma t)
        (covDerivAlong h gamma Y t) (covDerivAlong h gamma Y t)) :=
      Real.sqrt_le_sqrt (hmetric _)
    _ = Real.sqrt Lambda * Real.sqrt (g.inner (gamma t)
        (covDerivAlong h gamma Y t) (covDerivAlong h gamma Y t)) :=
      Real.sqrt_mul hLambda _
    _ ≤ _ := by
      rw [hdecomp]
      exact mul_le_mul_of_nonneg_left
        (sqrt_inner_add_le g (gamma t) (covDerivAlong g gamma Y t) A)
        (Real.sqrt_nonneg _)

theorem covDerivAlong_norm_le_of_connection_bound
    (g h : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (Y : ∀ t, TangentSpace I (gamma t)) (t : ℝ)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t)
    {Lambda A Q V W : ℝ} (hLambda : 0 ≤ Lambda) (hA : 0 ≤ A)
    (hmetric : ∀ z : TangentSpace I (gamma t),
      h.inner (gamma t) z z ≤ Lambda * g.inner (gamma t) z z)
    (hconnection : ∀ u w : TangentSpace I (gamma t),
      Real.sqrt (g.inner (gamma t)
        (CovariantDerivative.difference (metricCov h) (metricCov g) (gamma t) u w)
        (CovariantDerivative.difference (metricCov h) (metricCov g) (gamma t) u w)) ≤
        A * Real.sqrt (g.inner (gamma t) u u) * Real.sqrt (g.inner (gamma t) w w))
    (hY : Real.sqrt (g.inner (gamma t) (Y t) (Y t)) ≤ Q)
    (hvelocity : Real.sqrt (g.inner (gamma t)
      (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) ≤ V)
    (hderivative : Real.sqrt (g.inner (gamma t)
      (covDerivAlong g gamma Y t) (covDerivAlong g gamma Y t)) ≤ W) :
    Real.sqrt (h.inner (gamma t)
      (covDerivAlong h gamma Y t) (covDerivAlong h gamma Y t)) ≤
      Real.sqrt Lambda * (W + A * Q * V) := by
  have hQ : 0 ≤ Q := (Real.sqrt_nonneg _).trans hY
  refine (covDerivAlong_norm_le_of_metric_comparison
    g h gamma Y t hgamma hLambda hmetric).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  refine add_le_add hderivative ((hconnection _ _).trans ?_)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hY hA) hvelocity
    (Real.sqrt_nonneg _) (mul_nonneg hA hQ)

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
