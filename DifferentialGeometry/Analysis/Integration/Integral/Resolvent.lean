import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

set_option autoImplicit false

noncomputable section

open Complex Metric
open scoped NNReal

namespace spectrum

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem norm_normalized_circleIntegral_resolvent_sub_le (a b : A) {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : sphere c r ⊆ resolventSet ℂ a)
    (hb : sphere c r ⊆ resolventSet ℂ b) (K L : ℝ≥0)
    (hK : ∀ z ∈ sphere c r, ‖resolvent a z‖ ≤ K)
    (hL : ∀ z ∈ sphere c r, ‖resolvent b z‖ ≤ L) :
    ‖(2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), resolvent a z) -
        (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), resolvent b z)‖ ≤
      r * (K * ‖a - b‖ * L) := by
  have hai : CircleIntegrable (resolvent a) c r :=
    (show ContinuousOn (resolvent a) (sphere c r) from fun z hz =>
      (hasDerivAt_resolvent_const_left (ha hz)).continuousAt.continuousWithinAt).circleIntegrable hr
  have hbi : CircleIntegrable (resolvent b) c r :=
    (show ContinuousOn (resolvent b) (sphere c r) from fun z hz =>
      (hasDerivAt_resolvent_const_left (hb hz)).continuousAt.continuousWithinAt).circleIntegrable hr
  rw [← smul_sub, ← circleIntegral.integral_sub hai hbi]
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr
  intro z hz
  rw [resolvent_sub_resolvent (ha hz) (hb hz)]
  calc
    ‖resolvent a z * (a - b) * resolvent b z‖ ≤
        (‖resolvent a z‖ * ‖a - b‖) * ‖resolvent b z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (K * ‖a - b‖) * L := by
      gcongr
      · exact hK z hz
      · exact hL z hz

end spectrum
