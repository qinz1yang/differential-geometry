import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

noncomputable section

open Real
open scoped ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

def fluxShellWeight (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d * ((k + 1 : ℕ) : ℝ) *
    Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))

theorem fluxShellWeight_sum (d : ℕ) : Summable (fluxShellWeight d) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul (d + 1)
    (by norm_num : 0 < (4 : ℝ)⁻¹)
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hmul := hsucc.mul_left
    ((5 : ℝ) ^ d * Real.exp (4 : ℝ)⁻¹)
  have heq : fluxShellWeight d = fun k : ℕ =>
      (5 : ℝ) ^ d * Real.exp (4 : ℝ)⁻¹ *
        (((k + 1 : ℕ) : ℝ) ^ (d + 1) *
          Real.exp (-(4 : ℝ)⁻¹ * (((k + 1 : ℕ) : ℝ)))) := by
    funext k
    unfold fluxShellWeight
    rw [mul_pow]
    calc
      (5 ^ d * (((k + 1 : ℕ) : ℝ)) ^ d) * (((k + 1 : ℕ) : ℝ)) *
            Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)) =
          (5 ^ d * Real.exp (4 : ℝ)⁻¹) *
            ((((k + 1 : ℕ) : ℝ)) ^ (d + 1) *
              Real.exp (-(4 : ℝ)⁻¹ * (((k + 1 : ℕ) : ℝ)))) := by
        have hexp : Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)) =
            Real.exp (4 : ℝ)⁻¹ *
              Real.exp (-(4 : ℝ)⁻¹ * (((k + 1 : ℕ) : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
          norm_num
          ring
        rw [pow_succ, hexp]
        ring
      _ = _ := rfl
  rw [heq]
  simpa only [Function.comp_apply] using hmul

def fluxShellSeries (d : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (fluxShellWeight d k)

theorem fluxShellSeries_ne_top (d : ℕ) : fluxShellSeries d ≠ ∞ :=
  (fluxShellWeight_sum d).tsum_ofReal_ne_top

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
