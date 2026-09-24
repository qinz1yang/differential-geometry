import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

theorem hasDerivAt_gaussian_normalization (n : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => Real.exp (-(n / 2) * Real.log s -
        (n / 2) * Real.log (4 * Real.pi)))
      (-(n / (2 * t)) * Real.exp (-(n / 2) * Real.log t -
        (n / 2) * Real.log (4 * Real.pi))) t := by
  have h := (((Real.hasDerivAt_log ht.ne').const_mul (-(n / 2))).sub_const
    ((n / 2) * Real.log (4 * Real.pi))).exp
  apply h.congr_deriv
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end DifferentialGeometry.Analysis.Parabolic.Euclidean
