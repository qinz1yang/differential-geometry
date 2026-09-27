import DifferentialGeometry.Analysis.Calculus.Periodic.Smoothing



noncomputable section

open MeasureTheory Function ContinuousLinearMap
open scoped Convolution ContDiff

namespace DifferentialGeometry.Analysis


theorem smoothPeriodic_monotone (φ : ContDiffBump (0 : ℝ)) {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hm : Monotone ψ) : Monotone (smoothPeriodic φ ψ) := by
  have hi (x : ℝ) : Integrable (fun t => φ.normed volume t * ψ (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hc x
  intro x y hxy
  simp only [smoothPeriodic, convolution_def, lsmul_apply, smul_eq_mul]
  exact integral_mono (hi x) (hi y) (fun t =>
    mul_le_mul_of_nonneg_left (hm (sub_le_sub_right hxy t)) (φ.nonneg_normed t))


theorem smoothPeriodic_affinePeriodic (φ : ContDiffBump (0 : ℝ)) {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1) :
    ∀ t, smoothPeriodic φ ψ (t + 1) = smoothPeriodic φ ψ t + 1 := by
  have hi (x : ℝ) : Integrable (fun t => φ.normed volume t * ψ (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hc x
  intro x
  simp only [smoothPeriodic, convolution_def, lsmul_apply, smul_eq_mul]
  have heq : (fun t => φ.normed volume t * ψ (x + 1 - t)) =
      (fun t => φ.normed volume t * ψ (x - t) + φ.normed volume t) := by
    funext t
    rw [show x + 1 - t = (x - t) + 1 by ring, hp]
    ring
  rw [heq, integral_add (hi x) φ.integrable_normed, φ.integral_normed]

end DifferentialGeometry.Analysis
