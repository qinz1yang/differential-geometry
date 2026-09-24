import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.NormComparison
import DifferentialGeometry.Geometry.Geodesic.Local
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem covDerivAlong_velocity_norm_le_of_reference_geodesic
    (g h : SmoothRiemannianMetric I M) (beta : ℝ → M) (t : ℝ)
    (hbeta : IsGeodesicAt (I := I) g beta t)
    {Λ A V : ℝ} (hΛ : 0 ≤ Λ) (hA : 0 ≤ A)
    (hmetric : ∀ z : TangentSpace I (beta t),
      h.inner (beta t) z z ≤ Λ * g.inner (beta t) z z)
    (hconnection : ∀ u w : TangentSpace I (beta t),
      Real.sqrt (g.inner (beta t)
        (CovariantDerivative.difference (metricCov h) (metricCov g) (beta t) u w)
        (CovariantDerivative.difference (metricCov h) (metricCov g) (beta t) u w)) ≤
        A * Real.sqrt (g.inner (beta t) u u) * Real.sqrt (g.inner (beta t) w w))
    (hvelocity : Real.sqrt (g.inner (beta t)
      (mfderiv 𝓘(ℝ, ℝ) I beta t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I beta t (1 : ℝ))) ≤ V) :
    Real.sqrt (h.inner (beta t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)) ≤
      Real.sqrt Λ * (A * V ^ 2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hbetaC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 beta t :=
    (contMDiffAt_of_isGeodesicAt hbeta).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hbetaMD : MDifferentiableAt 𝓘(ℝ, ℝ) I beta t :=
    hbetaC2.mdifferentiableAt (by norm_num)
  have hacc : covDerivAlong g beta
      (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g beta t hbetaC2
      (IsGeodesicAt.hasGeodesicEquationAt (I := I) g hbeta)
  have hzero : Real.sqrt (g.inner (beta t)
      (covDerivAlong g beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)
      (covDerivAlong g beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t)) ≤ 0 := by
    rw [hacc]
    simp
  have hnorm := covDerivAlong_norm_le_of_connection_bound g h beta
    (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t
    hbetaMD hΛ hA hmetric hconnection hvelocity hvelocity hzero
  simpa only [zero_add, pow_two, mul_assoc] using hnorm

theorem abs_covDerivAlong_velocity_pairing_div_le_of_reference_geodesic
    (g h : SmoothRiemannianMetric I M) (beta : ℝ → M) (t : ℝ)
    (hbeta : IsGeodesicAt (I := I) g beta t)
    {Λ A V U b : ℝ} (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hb : 0 < b)
    (hmetric : ∀ z : TangentSpace I (beta t),
      h.inner (beta t) z z ≤ Λ * g.inner (beta t) z z)
    (hconnection : ∀ u w : TangentSpace I (beta t),
      Real.sqrt (g.inner (beta t)
        (CovariantDerivative.difference (metricCov h) (metricCov g) (beta t) u w)
        (CovariantDerivative.difference (metricCov h) (metricCov g) (beta t) u w)) ≤
        A * Real.sqrt (g.inner (beta t) u u) * Real.sqrt (g.inner (beta t) w w))
    (hvelocity : Real.sqrt (g.inner (beta t)
      (mfderiv 𝓘(ℝ, ℝ) I beta t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I beta t (1 : ℝ))) ≤ V)
    (w : TangentSpace I (beta t)) (hw : Real.sqrt (h.inner (beta t) w w) ≤ U) :
    |h.inner (beta t)
      (covDerivAlong h beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t) w / (2 * b)| ≤
      (Real.sqrt Λ * (A * V ^ 2) * U) / (2 * b) := by
  have hacc := covDerivAlong_velocity_norm_le_of_reference_geodesic
    g h beta t hbeta hΛ hA hmetric hconnection hvelocity
  have hpair := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    h (beta t) (covDerivAlong h beta
      (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) t) w
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hb)]
  apply div_le_div_of_nonneg_right _ (mul_pos (by norm_num) hb).le
  exact hpair.trans (mul_le_mul hacc hw (Real.sqrt_nonneg _) (by positivity))

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
