import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

private def leftRamp (R r : ℝ) := Real.smoothTransition (4 * r / R + 3)
private def rightRamp (R r : ℝ) := Real.smoothTransition (3 - 4 * r / R)

/-- A fixed smooth flattening of the original exponential height profile. -/
def flattenedExponentialProfile (R r : ℝ) : ℝ :=
  leftRamp R r * rightRamp R r * (Real.exp (-r) - 1) +
    (1 - leftRamp R r) * (Real.exp (R / 2) - 1) + (1 - rightRamp R r) * (Real.exp (-R / 2) - 1)

private theorem leftRamp_one {R r : ℝ} (hR : 0 < R) (hr : -R / 2 ≤ r) :
    leftRamp R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : -2 ≤ 4 * r / R := (le_div_iff₀ hR).mpr (by linarith)
  linarith

private theorem rightRamp_one {R r : ℝ} (hR : 0 < R) (hr : r ≤ R / 2) :
    rightRamp R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 4 * r / R ≤ 2 := (div_le_iff₀ hR).mpr (by linarith)
  linarith

private theorem leftRamp_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ -3 * R / 4) :
    leftRamp R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : 4 * r / R ≤ -3 := (div_le_iff₀ hR).mpr (by linarith)
  linarith

private theorem rightRamp_zero {R r : ℝ} (hR : 0 < R) (hr : 3 * R / 4 ≤ r) :
    rightRamp R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : 3 ≤ 4 * r / R := (le_div_iff₀ hR).mpr (by linarith)
  linarith

theorem contDiff_flattenedExponentialProfile (R : ℝ) : ContDiff ℝ ∞ (flattenedExponentialProfile R) := by
  unfold flattenedExponentialProfile leftRamp rightRamp
  fun_prop

theorem flattenedExponentialProfile_eq_exp {R r : ℝ} (hR : 0 < R)
    (hr : r ∈ Icc (-R / 2) (R / 2)) :
    flattenedExponentialProfile R r = Real.exp (-r) - 1 := by
  simp only [flattenedExponentialProfile, leftRamp_one hR hr.1,
    rightRamp_one hR hr.2, one_mul, sub_self, zero_mul, add_zero]

theorem flattenedExponentialProfile_eq_left {R r : ℝ} (hR : 0 < R) (hr : r ≤ -3 * R / 4) :
    flattenedExponentialProfile R r = (Real.exp (R / 2) - 1) := by
  have hrhalf : r ≤ R / 2 := by linarith
  have hright : rightRamp R r = 1 := rightRamp_one hR hrhalf
  simp only [flattenedExponentialProfile, leftRamp_zero hR hr, hright]
  ring

theorem flattenedExponentialProfile_eq_right {R r : ℝ} (hR : 0 < R) (hr : 3 * R / 4 ≤ r) :
    flattenedExponentialProfile R r = (Real.exp (-R / 2) - 1) := by
  have hrhalf : -R / 2 ≤ r := by linarith
  have hleft : leftRamp R r = 1 := leftRamp_one hR hrhalf
  simp only [flattenedExponentialProfile, hleft, rightRamp_zero hR hr]
  ring

private theorem side_values {R : ℝ} (hR : 0 < R) :
    0 < (Real.exp (R / 2) - 1) ∧ (Real.exp (-R / 2) - 1) < 0 := by
  constructor
  · exact sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr (half_pos hR))
  · exact sub_neg.mpr (by simpa using Real.exp_lt_exp.mpr (show -R / 2 < 0 by linarith))

private theorem positive_blend {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < s * a + (1 - s) * b := by
  by_cases h : s = 1
  · simpa [h] using ha
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hs.1 ha.le)
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hs.2 h)) hb)

theorem flattenedExponentialProfile_sign {R r : ℝ} (hR : 0 < R) :
    (flattenedExponentialProfile R r ≤ 0 ↔ 0 ≤ r) ∧
      (0 ≤ flattenedExponentialProfile R r ↔ r ≤ 0) := by
  obtain ⟨hL, hQ⟩ := side_values hR
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hraw : 0 < Real.exp (-r) - 1 :=
      sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr (neg_pos.mpr hr))
    have hp : 0 < flattenedExponentialProfile R r := by
      have hrhalf : r ≤ R / 2 := by linarith
      have hright : rightRamp R r = 1 := rightRamp_one hR hrhalf
      simpa only [flattenedExponentialProfile, hright, mul_one,
        sub_self, zero_mul, add_zero] using
        positive_blend (s := leftRamp R r) hraw hL
          (show leftRamp R r ∈ Icc (0 : ℝ) 1 from
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    constructor <;> constructor <;> intro h
    · exact False.elim (not_le_of_gt hp h)
    · exact False.elim (not_le_of_gt hr h)
    · exact hr.le
    · exact hp.le
  · subst r
    have hz := flattenedExponentialProfile_eq_exp hR (r := 0) (by constructor <;> linarith)
    simp only [neg_zero, Real.exp_zero, sub_self] at hz
    simp only [hz, le_refl, and_self]
  · have hraw : Real.exp (-r) - 1 < 0 :=
      sub_neg.mpr (by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hr))
    have hn : flattenedExponentialProfile R r < 0 := by
      have hh := positive_blend (neg_pos.mpr hraw) (neg_pos.mpr hQ)
        (show rightRamp R r ∈ Icc (0 : ℝ) 1 from
          ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
      rw [flattenedExponentialProfile, leftRamp_one hR (by linarith)]
      simp only [one_mul, sub_self, zero_mul, add_zero]
      nlinarith
    constructor <;> constructor <;> intro h
    · exact hr.le
    · exact hn.le
    · exact False.elim (not_le_of_gt hn h)
    · exact False.elim (not_le_of_gt hr h)

private theorem flattened_lower_left {R r : ℝ} (hR : 0 < R) (hr : r ≤ -R / 2) :
    (Real.exp (R / 2) - 1) ≤ flattenedExponentialProfile R r := by
  have hraw : (Real.exp (R / 2) - 1) ≤ Real.exp (-r) - 1 :=
    sub_le_sub_right (Real.exp_le_exp.mpr (by linarith)) 1
  rw [flattenedExponentialProfile, rightRamp_one hR (by linarith)]
  simp only [mul_one, sub_self, zero_mul, add_zero]
  have hh := mul_nonneg (show 0 ≤ leftRamp R r from Real.smoothTransition.nonneg _)
    (sub_nonneg.mpr hraw)
  nlinarith

theorem mem_central_interval_of_flattenedExponentialProfile_mem_Ico {R a r : ℝ} (hR : 0 < R)
    (ha : a < (Real.exp (R / 2) - 1)) (hr : flattenedExponentialProfile R r ∈ Ico (0 : ℝ) a) :
    r ∈ Ioo (-R / 2) (R / 2) := by
  have hn : r ≤ 0 := (flattenedExponentialProfile_sign hR).2.mp hr.1
  have hl : -R / 2 < r := by
    by_contra h
    have hh := flattened_lower_left hR (le_of_not_gt h)
    linarith [hr.2]
  exact ⟨hl, hn.trans_lt (half_pos hR)⟩

end DifferentialGeometry.Analysis
