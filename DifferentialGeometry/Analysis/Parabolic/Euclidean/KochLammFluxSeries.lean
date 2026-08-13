import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open Real

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

def klFluxWeight (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d *
    Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2)

private def klFluxLinWt (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d *
    Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ))

private theorem klFluxLin_sum (d : ℕ) : Summable (klFluxLinWt d) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul d
    (by norm_num : 0 < (8 : ℝ)⁻¹)
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hmul := hsucc.mul_left
    ((5 : ℝ) ^ d * Real.exp (8 : ℝ)⁻¹)
  convert hmul using 1
  funext k
  unfold klFluxLinWt
  simp only [Function.comp_apply, Nat.cast_succ]
  rw [mul_pow]
  calc
    5 ^ d * (k + 1 : ℝ) ^ d *
          Real.exp (-(8 : ℝ)⁻¹ * k) =
        (5 ^ d * Real.exp (8 : ℝ)⁻¹) *
          ((k + 1 : ℝ) ^ d *
            Real.exp (-(8 : ℝ)⁻¹ * (k + 1))) := by
      have hexp : Real.exp (8 : ℝ)⁻¹ *
          Real.exp (-(8 : ℝ)⁻¹ * (k + 1)) =
          Real.exp (-(8 : ℝ)⁻¹ * k) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring
    _ = _ := rfl

theorem klFluxWeight_le (d k : ℕ) :
    klFluxWeight d k ≤ klFluxLinWt d k := by
  have hk_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hkpos : 0 ≤ (k : ℝ) := by positivity
      have hkmul : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) :=
        mul_nonneg hkpos (sub_nonneg.mpr hk1)
      nlinarith
  unfold klFluxWeight klFluxLinWt
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [hk_sq])) (by positivity)

theorem klFluxWeight_sum (d : ℕ) : Summable (klFluxWeight d) := by
  exact Summable.of_nonneg_of_le
    (fun k ↦ by unfold klFluxWeight; positivity)
    (klFluxWeight_le d) (klFluxLin_sum d)

def klFluxSeries (d : ℕ) : ℝ :=
  ∑' k : ℕ, klFluxWeight d k

theorem klFluxSeries_nn (d : ℕ) : 0 ≤ klFluxSeries d := by
  unfold klFluxSeries
  exact tsum_nonneg fun k ↦ by unfold klFluxWeight; positivity

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
