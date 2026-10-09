/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Analysis.Calculus.SmoothTransition

/-!
# The regularized minimum used for corner rounding

`roundedMin ε a b = (a + b - |a - b|_ε) / 2`, where `|·|_ε = Real.smoothAbs ε` is the smooth
absolute value of the PC smooth Schoenflies library.  It is a smooth function of `(a, b)`, lies
between `min a b - ε` and `min a b`, and equals `min a b` whenever `ε ≤ |a - b|`.  Its partial
derivatives are the convex weights `1 - roundedMinWeight` and `roundedMinWeight`.

Its zero superlevel set is exactly the predicate of
`OpenPartialHomeomorph.smoothAbsQuadrantSet` (`roundedMin_nonneg_iff`).
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold.CornerRounding

/-- The regularized minimum `(a + b - |a - b|_ε) / 2`. -/
noncomputable def roundedMin (ε a b : ℝ) : ℝ :=
  (a + b - Real.smoothAbs ε (a - b)) / 2

/-- The weight of the second argument in the derivative of `roundedMin`. -/
noncomputable def roundedMinWeight (ε a b : ℝ) : ℝ :=
  (1 + deriv (Real.smoothAbs ε) (a - b)) / 2

private theorem min_eq_half (a b : ℝ) : min a b = (a + b - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem roundedMin_le_min {ε : ℝ} (hε : 0 < ε) (a b : ℝ) : roundedMin ε a b ≤ min a b := by
  have h := (Real.smoothAbs.sub_abs_mem_Icc hε (a - b)).1
  rw [min_eq_half, roundedMin]
  linarith

theorem min_sub_le_roundedMin {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    min a b - ε ≤ roundedMin ε a b := by
  have h := (Real.smoothAbs.sub_abs_mem_Icc hε (a - b)).2
  rw [min_eq_half, roundedMin]
  linarith

theorem roundedMin_eq_min {ε a b : ℝ} (hε : 0 < ε) (h : ε ≤ |a - b|) :
    roundedMin ε a b = min a b := by
  rw [min_eq_half, roundedMin, Real.smoothAbs.eq_abs_of_le hε h]

theorem roundedMin_nonneg_iff {ε a b : ℝ} :
    0 ≤ roundedMin ε a b ↔ Real.smoothAbs ε (a - b) ≤ a + b := by
  rw [roundedMin]
  constructor <;> intro h <;> linarith

theorem roundedMin_nonpos_iff {ε a b : ℝ} :
    roundedMin ε a b ≤ 0 ↔ a + b ≤ Real.smoothAbs ε (a - b) := by
  rw [roundedMin]
  constructor <;> intro h <;> linarith

theorem nonneg_of_roundedMin_nonneg {ε a b : ℝ} (hε : 0 < ε) (h : 0 ≤ roundedMin ε a b) :
    0 ≤ a ∧ 0 ≤ b := by
  have hm := h.trans (roundedMin_le_min hε a b)
  exact ⟨hm.trans (min_le_left a b), hm.trans (min_le_right a b)⟩

theorem roundedMin_nonpos_of_nonpos {ε a b : ℝ} (hε : 0 < ε) (h : a ≤ 0 ∨ b ≤ 0) :
    roundedMin ε a b ≤ 0 := by
  rcases h with h | h
  · exact (roundedMin_le_min hε a b).trans ((min_le_left a b).trans h)
  · exact (roundedMin_le_min hε a b).trans ((min_le_right a b).trans h)

theorem roundedMin_neg_of_eq_neg {ε : ℝ} (hε : 0 < ε) (a : ℝ) : roundedMin ε a (-a) < 0 := by
  have h := Real.smoothAbs.pos hε (a - -a)
  rw [roundedMin]
  linarith

/-- Band where `roundedMin` differs from `min`. -/
theorem abs_sub_lt_of_roundedMin_ne_min {ε a b : ℝ} (hε : 0 < ε)
    (h : roundedMin ε a b ≠ min a b) : |a - b| < ε := by
  by_contra hab
  exact h (roundedMin_eq_min hε (not_lt.mp hab))

private theorem add_lt_three_of_abs_sub_lt {ε a b : ℝ} (hε : 0 < ε) (hab : |a - b| < ε)
    (h : a + b ≤ Real.smoothAbs ε (a - b)) : a + b < 3 * ε := by
  have h2 := (Real.smoothAbs.sub_abs_mem_Icc hε (a - b)).2
  linarith

/-- A removed point of the quadrant lies in the thin corner band. -/
theorem band_of_roundedMin_neg {ε a b : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : roundedMin ε a b < 0) : |a - b| < ε ∧ a + b < 3 * ε := by
  have hab : |a - b| < ε := by
    apply abs_sub_lt_of_roundedMin_ne_min hε
    intro he
    rw [he] at h
    exact absurd (le_min ha hb) (not_le.mpr h)
  exact ⟨hab, add_lt_three_of_abs_sub_lt hε hab (roundedMin_nonpos_iff.mp h.le)⟩

/-- An added point of the complementary side lies in the thin corner band. -/
theorem band_of_roundedMin_nonpos {ε a b : ℝ} (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (h : roundedMin ε a b ≤ 0) : |a - b| < ε ∧ a + b < 3 * ε := by
  have hab : |a - b| < ε := by
    apply abs_sub_lt_of_roundedMin_ne_min hε
    intro he
    rw [he] at h
    exact absurd (lt_min ha hb) (not_lt.mpr h)
  exact ⟨hab, add_lt_three_of_abs_sub_lt hε hab (roundedMin_nonpos_iff.mp h)⟩

/-- A zero of `roundedMin` inside the band `|a - b| < ε` is a nonnegative pair with small sum. -/
theorem band_of_roundedMin_eq_zero {ε a b : ℝ} (hε : 0 < ε) (hab : |a - b| < ε)
    (h : roundedMin ε a b = 0) : 0 ≤ a ∧ 0 ≤ b ∧ a + b < 3 * ε := by
  obtain ⟨ha, hb⟩ := nonneg_of_roundedMin_nonneg hε h.ge
  exact ⟨ha, hb, add_lt_three_of_abs_sub_lt hε hab (roundedMin_nonpos_iff.mp h.le)⟩

theorem roundedMinWeight_mem_Icc (ε a b : ℝ) : roundedMinWeight ε a b ∈ Icc (0 : ℝ) 1 := by
  have h := abs_le.mp (Real.smoothAbs.abs_deriv_le_one ε (a - b))
  rw [roundedMinWeight]
  constructor <;> linarith [h.1, h.2]

theorem roundedMinWeight_eq_one {ε a b : ℝ} (hε : 0 < ε) (h : ε ≤ a - b) :
    roundedMinWeight ε a b = 1 := by
  have hz : (ε - (a - b)) / (2 * ε) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [roundedMinWeight, Real.smoothAbs.deriv, Real.smoothTransition.zero_of_nonpos hz]
  norm_num

theorem roundedMinWeight_eq_zero {ε a b : ℝ} (hε : 0 < ε) (h : ε ≤ b - a) :
    roundedMinWeight ε a b = 0 := by
  have hz : 1 ≤ (ε - (a - b)) / (2 * ε) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)]
    linarith
  rw [roundedMinWeight, Real.smoothAbs.deriv, Real.smoothTransition.one_of_one_le hz]
  norm_num

theorem contDiff_roundedMin (ε : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => roundedMin ε p.1 p.2) := by
  unfold roundedMin
  exact ((contDiff_fst.add contDiff_snd).sub
    ((Real.smoothAbs.contDiff ε).comp (contDiff_fst.sub contDiff_snd))).div_const 2

end DifferentialGeometry.Topology.Manifold.CornerRounding
