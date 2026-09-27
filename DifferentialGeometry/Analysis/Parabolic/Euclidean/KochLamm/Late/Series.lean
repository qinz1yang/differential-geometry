import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open Real

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

def kochLammLateWeight (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d * Real.exp (-((k : ℝ) ^ 2) / 4)

private def kochLammLateLinWt (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d *
    Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ))

private theorem kochLammLateLin_sum (d : ℕ) : Summable (kochLammLateLinWt d) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul d
    (by norm_num : 0 < (4 : ℝ)⁻¹)
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hmul := hsucc.mul_left
    ((5 : ℝ) ^ d * Real.exp (4 : ℝ)⁻¹)
  apply hmul.congr
  intro k
  symm
  unfold kochLammLateLinWt
  simp only [Function.comp_apply, Nat.cast_succ]
  rw [mul_pow]
  calc
    5 ^ d * (k + 1 : ℝ) ^ d *
          Real.exp (-(4 : ℝ)⁻¹ * k) =
        (5 ^ d * Real.exp (4 : ℝ)⁻¹) *
          ((k + 1 : ℝ) ^ d *
            Real.exp (-(4 : ℝ)⁻¹ * (k + 1))) := by
      have hexp : Real.exp (4 : ℝ)⁻¹ *
          Real.exp (-(4 : ℝ)⁻¹ * (k + 1)) =
          Real.exp (-(4 : ℝ)⁻¹ * k) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring
    _ = _ := rfl

theorem kochLammLateWeight_le (d k : ℕ) :
    kochLammLateWeight d k ≤ kochLammLateLinWt d k := by
  have hk_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hkpos : 0 ≤ (k : ℝ) := by positivity
      have hkmul : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) :=
        mul_nonneg hkpos (sub_nonneg.mpr hk1)
      nlinarith
  unfold kochLammLateWeight kochLammLateLinWt
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [hk_sq])) (by positivity)

theorem kochLammLateWeight_sum (d : ℕ) : Summable (kochLammLateWeight d) := by
  exact Summable.of_nonneg_of_le
    (fun k ↦ by unfold kochLammLateWeight; positivity)
    (kochLammLateWeight_le d) (kochLammLateLin_sum d)

def kochLammLateSeries (d : ℕ) : ℝ :=
  ∑' k : ℕ, kochLammLateWeight d k

theorem kochLammLateSeries_nn (d : ℕ) : 0 ≤ kochLammLateSeries d := by
  unfold kochLammLateSeries
  exact tsum_nonneg fun k ↦ by unfold kochLammLateWeight; positivity

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
