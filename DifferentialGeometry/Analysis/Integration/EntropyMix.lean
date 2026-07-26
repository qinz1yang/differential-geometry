import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Scalar entropy mixing estimates

This file records the elementary subadditivity estimate for the continuous
extension of `x ↦ -x log x` on the nonnegative half-line.
-/

namespace DifferentialGeometry.Analysis.Integration

/-- The entropy integrand `-x log x` is subadditive on nonnegative inputs. -/
theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_add, Real.negMulLog_zero, zero_add]
    exact le_rfl
  rcases hb.eq_or_lt with rfl | hb
  · simp only [add_zero, Real.negMulLog_zero, add_zero]
    exact le_rfl
  have hla : Real.log a ≤ Real.log (a + b) :=
    Real.log_le_log ha (le_add_of_nonneg_right hb.le)
  have hlb : Real.log b ≤ Real.log (a + b) :=
    Real.log_le_log hb (le_add_of_nonneg_left ha.le)
  have hama : a * Real.log a ≤ a * Real.log (a + b) :=
    mul_le_mul_of_nonneg_left hla ha.le
  have hbmb : b * Real.log b ≤ b * Real.log (a + b) :=
    mul_le_mul_of_nonneg_left hlb hb.le
  rw [Real.negMulLog, Real.negMulLog, Real.negMulLog]
  nlinarith

end DifferentialGeometry.Analysis.Integration
