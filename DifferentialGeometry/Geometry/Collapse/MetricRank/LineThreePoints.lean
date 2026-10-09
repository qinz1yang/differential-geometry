import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Three points on a line (review 75, section C.4, S-X144 group G1)

The real-line core of the line exclusion `not_splitting_ge_two_of_line_ball`: three real numbers
whose pairwise distances all lie in `[s - e, s + e]` force `s + e ≥ 2 (s - e)`, because the
largest of the three gaps is the sum of the other two. With `s = 5` and `e ≤ 19/25`
(`e = 5 β + ε_m`, `β ≤ 3/20`, `ε_m ≤ 1/100`) the numerical hypothesis `5 + e < 2 (5 - e)` holds.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

/-- Three reals with all pairwise distances in `[s - e, s + e]` and `s + e < 2 (s - e)`: impossible
(C.4, the largest gap is the sum of the two others). -/
theorem not_three_points_on_line_SMR {s e a b c : ℝ} (hse : s + e < 2 * (s - e))
    (hab₁ : s - e ≤ |a - b|) (hab₂ : |a - b| ≤ s + e)
    (hbc₁ : s - e ≤ |b - c|) (hbc₂ : |b - c| ≤ s + e)
    (hac₁ : s - e ≤ |a - c|) (hac₂ : |a - c| ≤ s + e) : False := by
  have h1 := abs_le.mp hab₂
  have h2 := abs_le.mp hbc₂
  have h3 := abs_le.mp hac₂
  rcases le_abs'.mp hab₁ with h4 | h4 <;> rcases le_abs'.mp hbc₁ with h5 | h5 <;>
    rcases le_abs'.mp hac₁ with h6 | h6 <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- The family form of `not_three_points_on_line_SMR`. -/
theorem not_three_points_on_line_family_SMR {s e : ℝ} (hse : s + e < 2 * (s - e)) (x : Fin 3 → ℝ)
    (h : ∀ i j : Fin 3, i ≠ j → s - e ≤ |x i - x j| ∧ |x i - x j| ≤ s + e) : False :=
  not_three_points_on_line_SMR hse (h 0 1 (by decide)).1 (h 0 1 (by decide)).2
    (h 1 2 (by decide)).1 (h 1 2 (by decide)).2 (h 0 2 (by decide)).1 (h 0 2 (by decide)).2

/-- The numerical hypothesis of C.4 for `s = 5`, `e ≤ 19/25`. -/
theorem five_add_lt_two_mul_five_sub_SMR {e : ℝ} (he : e ≤ 19 / 25) : 5 + e < 2 * (5 - e) := by
  linarith

/-- **Consumer (explicit numbers).** Fix two reals at distance exactly `5`; no third real has both
distances to them in `[5 - 19/25, 5 + 19/25]`. -/
theorem no_third_point_at_distance_five_SMR (a c : ℝ)
    (h₁ : 106 / 25 ≤ |c - a| ∧ |c - a| ≤ 144 / 25)
    (h₂ : 106 / 25 ≤ |c - (a + 5)| ∧ |c - (a + 5)| ≤ 144 / 25) : False := by
  have h0 : |a - (a + 5)| = 5 := by
    rw [show a - (a + 5) = -5 by ring, abs_neg]
    norm_num
  refine not_three_points_on_line_SMR (s := 5) (e := 19 / 25) (a := a) (b := a + 5) (c := c)
    (five_add_lt_two_mul_five_sub_SMR le_rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h0]; norm_num
  · rw [h0]; norm_num
  · rw [abs_sub_comm]; linarith [h₂.1]
  · rw [abs_sub_comm]; linarith [h₂.2]
  · rw [abs_sub_comm]; linarith [h₁.1]
  · rw [abs_sub_comm]; linarith [h₁.2]

end GC.MetricGeometry
