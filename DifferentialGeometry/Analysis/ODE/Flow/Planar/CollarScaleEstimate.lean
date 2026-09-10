import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace DifferentialGeometry.Analysis

theorem exists_uniform_collar_error_threshold (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ε < 1 / 200000 ∧ 92354 * ε + C * ε < 1 ∧ C * ε * Real.sqrt (1 + ε) < 1 ∧
      ∃ B : ℝ, 0 ≤ B ∧ B < 1 - 92354 * ε ∧
        ∀ Q₀ Q₁ : ℝ, 0 < Q₀ → 0 < Q₁ → |Q₀ / Q₁ - 1| ≤ C * ε →
        ∀ Q : ℝ, Q = Q₀ ∨ Q = Q₁ →
          2 * (C * ε / Real.sqrt Q₀) < (Real.sqrt Q)⁻¹ ∧
          ∀ d : ℝ, 1 / 2 ≤ d →
            (A / d) * Real.sqrt Q * (1 + 92354 * ε) *
              (C * ε / Real.sqrt Q₀) ≤ B := by
  let ε₀ : ℝ := min (1 / 200000) (min (1 / (8 * C)) (1 / (12 * A * C)))
  have hε₀ : 0 < ε₀ := lt_min (by norm_num)
    (lt_min (one_div_pos.mpr (mul_pos (by norm_num) hC))
      (one_div_pos.mpr (mul_pos (mul_pos (by norm_num) hA) hC)))
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hεnonneg hε
  have heps : ε < 1 / 200000 := hε.trans_le (min_le_left _ _)
  have hepsC : ε < 1 / (8 * C) := hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsAC : ε < 1 / (12 * A * C) := hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hr : 92354 * ε < 1 / 2 := by linarith only [heps]
  have hE : C * ε < 1 / 8 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hC)).mp hepsC
    nlinarith only [h]
  have hE0 : 0 ≤ C * ε := mul_nonneg hC.le hεnonneg
  have hrootε : Real.sqrt (1 + ε) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith only [heps]
  have htrans : C * ε * Real.sqrt (1 + ε) < 1 :=
    (mul_le_mul_of_nonneg_left hrootε hE0).trans_lt (by linarith only [hE])
  let B : ℝ := 6 * A * (C * ε)
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) hA.le) hE0
  have hBhalf : B < 1 / 2 := by
    have h := (lt_div_iff₀ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 12) hA) hC)).mp hepsAC
    dsimp only [B]
    nlinarith only [h]
  refine ⟨heps, by linarith only [hr, hE], htrans, B, hB0,
    by linarith only [hBhalf, hr], ?_⟩
  intro Q₀ Q₁ hQ₀ hQ₁ hratio Q hwhich
  have hQ : 0 < Q := by rcases hwhich with rfl | rfl <;> assumption
  have hQbound : Q ≤ 4 * Q₀ := by
    rcases hwhich with hwhich | hwhich
    · rw [hwhich]
      linarith only [hQ₀]
    · have hlow : (1 / 2 : ℝ) ≤ Q₀ / Q₁ := by
        have h := (abs_le.mp hratio).1
        linarith only [h, hE]
      have h := (le_div_iff₀ hQ₁).mp hlow
      rw [hwhich]
      linarith only [h, hQ₀]
  have hq₀ : 0 < Real.sqrt Q₀ := Real.sqrt_pos.mpr hQ₀
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hroot : Real.sqrt Q ≤ 2 * Real.sqrt Q₀ := by
    calc
      _ ≤ Real.sqrt (4 * Q₀) := Real.sqrt_le_sqrt hQbound
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hquot : 0 ≤ C * ε / Real.sqrt Q₀ := div_nonneg hE0 hq₀.le
  constructor
  · rw [← one_div]
    apply (lt_div_iff₀ hq).mpr
    calc
      _ ≤ (2 * (C * ε / Real.sqrt Q₀)) * (2 * Real.sqrt Q₀) :=
        mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num) hquot)
      _ = 4 * (C * ε) := by field_simp; ring
      _ < 1 := by linarith only [hE]
  · intro d hd
    have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
    have hdiv : A / d ≤ 2 * A := by
      apply (div_le_iff₀ hdpos).mpr
      nlinarith only [hd, hA]
    have hcoeff : (A / d) * Real.sqrt Q ≤ 4 * A * Real.sqrt Q₀ := by
      calc
        _ ≤ (2 * A) * Real.sqrt Q := mul_le_mul_of_nonneg_right hdiv hq.le
        _ ≤ (2 * A) * (2 * Real.sqrt Q₀) :=
          mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num) hA.le)
        _ = _ := by ring
    have h1r : 0 ≤ 1 + 92354 * ε := by positivity
    calc
      _ ≤ (4 * A * Real.sqrt Q₀) * (1 + 92354 * ε) * (C * ε / Real.sqrt Q₀) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff h1r) hquot
      _ = 4 * A * (1 + 92354 * ε) * (C * ε) := by field_simp
      _ ≤ B := by
        have hAE : 0 ≤ A * (C * ε) := mul_nonneg hA.le hE0
        dsimp only [B]
        nlinarith only [hr.le, hAE]

end DifferentialGeometry.Analysis
