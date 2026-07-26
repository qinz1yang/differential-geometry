import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian-polynomial summation for terminal Koch--Lamm flux shells

The quantitative cover grows polynomially like `(5(k+1))^d`, while the
split first-derivative Gaussian contributes `exp (-k^2/8)`.  Their product is
summable with a finite constant depending only on the dimension.
-/

noncomputable section

open Real

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

/-- Exact Gaussian-polynomial weight of the `k`-th terminal flux shell. -/
def klFluxWeight (d k : ℕ) : ℝ :=
  (5 * ((k + 1 : ℕ) : ℝ)) ^ d *
    Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2)

/-- Linear-exponential majorant used only to prove summability. -/
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

/-- The exact Gaussian shell weight is bounded by its linear-exponential
majorant. -/
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

/-- Polynomial shell growth is summable against the split flux Gaussian. -/
theorem klFluxWeight_sum (d : ℕ) : Summable (klFluxWeight d) := by
  exact Summable.of_nonneg_of_le
    (fun k ↦ by unfold klFluxWeight; positivity)
    (klFluxWeight_le d) (klFluxLin_sum d)

/-- Finite dimension-dependent mass of the terminal flux shell majorant. -/
def klFluxSeries (d : ℕ) : ℝ :=
  ∑' k : ℕ, klFluxWeight d k

/-- The terminal flux shell-series constant is nonnegative. -/
theorem klFluxSeries_nn (d : ℕ) : 0 ≤ klFluxSeries d := by
  unfold klFluxSeries
  exact tsum_nonneg fun k ↦ by unfold klFluxWeight; positivity

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
