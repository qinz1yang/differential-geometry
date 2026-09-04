import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

section DirectedRadii

def openRadius (j l : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1))

theorem two_pow_lt_openRadius (j l : ℕ) :
    (2 : ℝ) ^ j < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  dsimp [openRadius]
  calc
    (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
    _ < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) :=
      mul_lt_mul_of_pos_left (by linarith) hpow

theorem openRadius_pos (j l : ℕ) :
    0 < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  dsimp [openRadius]
  nlinarith [mul_pos hpow (by linarith : (0 : ℝ) < 1 + (1 / 2 : ℝ) ^ (l + 1))]

theorem openRadius_succ_lt (j l : ℕ) :
    openRadius j (l + 1) < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [openRadius]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

def midRadius (j l : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (1 + (((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2))

theorem openRadius_succ_lt_midRadius (j l : ℕ) :
    openRadius j (l + 1) < midRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [openRadius, midRadius]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

theorem midRadius_lt_openRadius (j l : ℕ) :
    midRadius j l < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [openRadius, midRadius]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

theorem midRadius_le_two_pow_succ (j l : ℕ) :
    midRadius j l ≤ (2 : ℝ) ^ (j + 1) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    midRadius j l = (2 : ℝ) ^ j *
        (1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2) := by
      rfl
    _ ≤ (2 : ℝ) ^ j * (1 + (1 + 1) / 2) := by
      have hinner :
          1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2
            ≤ 1 + (1 + 1) / 2 := by
        linarith
      exact mul_le_mul_of_nonneg_left hinner hpow.le
    _ = (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ']
      ring

theorem midRadius_le_zero (j l : ℕ) :
    midRadius j l ≤ midRadius j 0 := by
  have hpow : 0 ≤ (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  dsimp [midRadius]
  refine mul_le_mul_of_nonneg_left ?_ hpow
  nlinarith

theorem half_pow_succ_le_half (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
  have hpow : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa using hpow

theorem sqrt_one_add_mul_openRadius_succ_lt_two_pow {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * openRadius j (l + 1) < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 3 / 2 := by
    have hlt : 1 + a < (3 / 2 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail_le : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  have hR_pos : 0 < openRadius j (l + 1) := openRadius_pos j (l + 1)
  have hR_le :
      openRadius j (l + 1) ≤ (5 / 4 : ℝ) * (2 : ℝ) ^ j := by
    dsimp [openRadius]
    nlinarith
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * openRadius j (l + 1)
        < (3 / 2 : ℝ) * openRadius j (l + 1) :=
          mul_lt_mul_of_pos_right hsqrt_lt hR_pos
    _ ≤ (3 / 2 : ℝ) * ((5 / 4 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hR_le (by norm_num)
    _ = (15 / 8 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono

theorem sqrt_one_add_mul_midRadius_lt_two_pow {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRadius j l < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 5 / 4 := by
    have hlt : 1 + a < (5 / 4 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((5 / 4 : ℝ) ^ 2) = 5 / 4 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmid_pos : 0 < midRadius j l := by
    dsimp [midRadius]
    positivity
  have hmid_le : midRadius j l ≤ (11 / 8 : ℝ) * (2 : ℝ) ^ j := by
    dsimp [midRadius]
    nlinarith [show 0 ≤ (2 : ℝ) ^ j by positivity]
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * midRadius j l
        < (5 / 4 : ℝ) * midRadius j l := mul_lt_mul_of_pos_right hsqrt_lt hmid_pos
    _ ≤ (5 / 4 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hmid_le (by norm_num)
    _ = (55 / 32 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith [show 0 < (2 : ℝ) ^ j by positivity]
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono

theorem sqrt_one_add_mul_midRadius_lt_next_openRadius {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRadius j l < openRadius (j + 1) l := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg _
  have hle_mid0 : Real.sqrt (1 + a) * midRadius j l ≤ Real.sqrt (1 + a) * midRadius j 0 :=
    mul_le_mul_of_nonneg_left (midRadius_le_zero j l) hsqrt_nonneg
  have hlt_step : Real.sqrt (1 + a) * midRadius j 0 < (2 : ℝ) ^ (j + 1) := by
    simpa using sqrt_one_add_mul_midRadius_lt_two_pow j 0 ha0 ha2
  exact lt_trans (lt_of_le_of_lt hle_mid0 hlt_step) (two_pow_lt_openRadius (j + 1) l)

end DirectedRadii

end CheegerGromovCompactness
end DifferentialGeometry
