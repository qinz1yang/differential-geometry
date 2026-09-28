import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Analysis

theorem normalized_cost_comparison {x y C u v ε δ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C)
    (hv : 0 < v) (huv : v ≤ u) (hratio : u ≤ (1 + ε) * v)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4) (hδ : 4 * ε ≤ δ)
    (hxy : x ≤ (1 + ε) * y + C)
    (hyx : y ≤ (1 + ε) * x + C) :
    x / (2 * v) ≤ (1 + δ) * y / (2 * u) + C / u ∧
      y / (2 * u) ≤ (1 + δ) * x / (2 * v) + C / u := by
  have hu : 0 < u := hv.trans_le huv
  have hedelta : ε ≤ δ := by linarith
  have hcoef : (1 + ε) ^ 2 ≤ 1 + δ := by nlinarith
  have hcoefC : 1 + ε ≤ 2 := by linarith
  have hpoly : (1 + ε) ^ 2 * y + (1 + ε) * C ≤
      (1 + δ) * y + 2 * C := by
    exact add_le_add (mul_le_mul_of_nonneg_right hcoef hy)
      (mul_le_mul_of_nonneg_right hcoefC hC)
  have hcross : x * u ≤ ((1 + δ) * y + 2 * C) * v := by
    have hterm : 0 ≤ (1 + ε) * y + C := by positivity
    calc
      x * u ≤ ((1 + ε) * y + C) * u :=
        mul_le_mul_of_nonneg_right hxy hu.le
      _ ≤ ((1 + ε) * y + C) * ((1 + ε) * v) :=
        mul_le_mul_of_nonneg_left hratio hterm
      _ = ((1 + ε) ^ 2 * y + (1 + ε) * C) * v := by ring
      _ ≤ ((1 + δ) * y + 2 * C) * v :=
        mul_le_mul_of_nonneg_right hpoly hv.le
  constructor
  · have hdiv : x / (2 * v) ≤ ((1 + δ) * y + 2 * C) / (2 * u) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hcross]
    refine hdiv.trans_eq ?_
    field_simp [hu.ne']
  · have hcoeff : (1 + ε) * x ≤ (1 + δ) * x :=
      mul_le_mul_of_nonneg_right (add_le_add_right hedelta 1) hx
    have hnum : 0 ≤ (1 + δ) * x := mul_nonneg (by linarith) hx
    have hden : 0 < 2 * v := by positivity
    calc
      y / (2 * u) ≤ ((1 + ε) * x + C) / (2 * u) :=
        div_le_div_of_nonneg_right hyx (by positivity)
      _ = (1 + ε) * x / (2 * u) + C / (2 * u) := add_div _ _ _
      _ ≤ (1 + δ) * x / (2 * u) + C / (2 * u) :=
        add_le_add (div_le_div_of_nonneg_right hcoeff (by positivity)) le_rfl
      _ ≤ (1 + δ) * x / (2 * v) + C / u := by
        exact add_le_add
          (div_le_div_of_nonneg_left hnum hden
            (mul_le_mul_of_nonneg_left huv (by norm_num)))
          (div_le_div_of_nonneg_left hC hu (by linarith))

end DifferentialGeometry.Analysis
