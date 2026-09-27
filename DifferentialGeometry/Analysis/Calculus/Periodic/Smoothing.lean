import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution









noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Function Metric ContinuousLinearMap
open scoped Topology ContDiff Convolution NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


def smoothPeriodic (φ : ContDiffBump (0 : ℝ)) (f : ℝ → F) : ℝ → F :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

omit [CompleteSpace F] in
theorem smoothPeriodic_contDiff (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F}
    (hf : Continuous f) : ContDiff ℝ ∞ (smoothPeriodic φ f) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

omit [CompleteSpace F] in
theorem smoothPeriodic_periodic (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F} {T : ℝ}
    (hf : Periodic f T) : Periodic (smoothPeriodic φ f) T := by
  intro x
  simp only [smoothPeriodic, convolution_def, lsmul_apply]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [show x + T - t = (x - t) + T by ring, hf]

@[simp] theorem smoothPeriodic_const (φ : ContDiffBump (0 : ℝ)) (v : F) :
    smoothPeriodic φ (fun _ => v) = fun _ => v := by
  funext x
  exact φ.normed_convolution_eq_right (fun _ _ => rfl)


theorem dist_smoothPeriodic_le (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F}
    (hf : Continuous f) {x ε : ℝ}
    (h : ∀ y ∈ Metric.ball x φ.rOut, dist (f y) (f x) ≤ ε) :
    dist (smoothPeriodic φ f x) (f x) ≤ ε :=
  φ.dist_normed_convolution_le hf.aestronglyMeasurable h

omit [CompleteSpace F] in
theorem smoothPeriodic_lipschitz (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) : LipschitzWith C (smoothPeriodic φ f) := by
  have hi (x : ℝ) : Integrable (fun t => φ.normed volume t • f (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf.continuous x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [smoothPeriodic, convolution_def, lsmul_apply, dist_eq_norm]
  rw [← integral_sub (hi x) (hi y)]
  calc
    ‖∫ t, φ.normed volume t • f (x - t) - φ.normed volume t • f (y - t)‖ ≤
        ∫ t, φ.normed volume t * ((C : ℝ) * ‖x - y‖) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul (x - t) (y - t)
    _ = (C : ℝ) * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

end DifferentialGeometry.Analysis
