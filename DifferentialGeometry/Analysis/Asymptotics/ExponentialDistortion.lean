import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Analysis.Asymptotics

private theorem exp_neg_difference_le
    {x y : ℝ} :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| * Real.exp (-min x y) := by
  by_cases hxy : x ≤ y
  · have hlin : 1 - Real.exp (-(y - x)) ≤ y - x := by
      have h := Real.add_one_le_exp (-(y - x))
      linarith
    have hfactor : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
      rw [show -y = -x + (-(y - x)) by ring, Real.exp_add]
    have hsign : Real.exp (-y) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      |Real.exp (-x) - Real.exp (-y)| =
          Real.exp (-x) * (1 - Real.exp (-(y - x))) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hsign), hfactor]
        ring
      _ ≤ Real.exp (-x) * (y - x) :=
        mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
      _ = |x - y| * Real.exp (-min x y) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy), min_eq_left hxy]
        ring
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hlin : 1 - Real.exp (-(x - y)) ≤ x - y := by
      have h := Real.add_one_le_exp (-(x - y))
      linarith
    have hfactor : Real.exp (-x) = Real.exp (-y) * Real.exp (-(x - y)) := by
      rw [show -x = -y + (-(x - y)) by ring, Real.exp_add]
    have hsign : Real.exp (-x) ≤ Real.exp (-y) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      |Real.exp (-x) - Real.exp (-y)| =
          Real.exp (-y) * (1 - Real.exp (-(x - y))) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hsign), hfactor]
        ring
      _ ≤ Real.exp (-y) * (x - y) :=
        mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
      _ = |x - y| * Real.exp (-min x y) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hyx), min_eq_right hyx]
        ring

private theorem exp_neg_min_le_three_mul
    {x y δ e : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hδ1 : δ ≤ 1) (he1 : e ≤ 1)
    (hxy : y ≤ (1 + δ) * x + e) :
    Real.exp (-min x y) ≤ 3 * Real.exp (-(y / 2)) := by
  have hcoef : 1 + δ ≤ 2 := by linarith
  have hmul : (1 + δ) * x ≤ 2 * x :=
    mul_le_mul_of_nonneg_right hcoef hx
  have hxmin : (y - 1) / 2 ≤ x := by linarith
  have hymin : (y - 1) / 2 ≤ y := by linarith
  have hmin : (y - 1) / 2 ≤ min x y := le_min hxmin hymin
  have hexp_arg : -(min x y) ≤ -(y - 1) / 2 := by linarith
  have hexp_le : Real.exp (-min x y) ≤ Real.exp (-(y - 1) / 2) :=
    Real.exp_le_exp.mpr hexp_arg
  have hsplit : Real.exp (-(y - 1) / 2) =
      Real.exp (1 / 2) * Real.exp (-(y / 2)) := by
    rw [show -(y - 1) / 2 = (1 / 2 : ℝ) + -(y / 2) by ring, Real.exp_add]
  have hexp_half : Real.exp (1 / 2) ≤ 3 := by
    calc
      Real.exp (1 / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 := Real.exp_one_lt_three.le
  rw [hsplit] at hexp_le
  exact hexp_le.trans (mul_le_mul_of_nonneg_right hexp_half (Real.exp_pos _).le)

private theorem mul_exp_neg_half_le_four_mul_exp_neg_quarter
    {y : ℝ} :
    y * Real.exp (-(y / 2)) ≤ 4 * Real.exp (-(y / 4)) := by
  have hbase := Real.mul_exp_neg_le_exp_neg_one (y / 4)
  have hone : Real.exp (-1) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hbase' : (y / 4) * Real.exp (-(y / 4)) ≤ 1 := hbase.trans hone
  have hsplit : Real.exp (-(y / 2)) =
      Real.exp (-(y / 4)) * Real.exp (-(y / 4)) := by
    rw [show -(y / 2) = -(y / 4) + -(y / 4) by ring, Real.exp_add]
  rw [hsplit]
  have hmul := mul_le_mul_of_nonneg_right hbase' (Real.exp_pos (-(y / 4))).le
  nlinarith [hmul]

private theorem exp_neg_half_le_exp_neg_quarter
    {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(y / 2)) ≤ Real.exp (-(y / 4)) := by
  exact Real.exp_le_exp.mpr (by linarith)

theorem abs_exp_neg_sub_exp_neg_le
    {x y δ e : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1)
    (hxy : x ≤ (1 + δ) * y + e)
    (hyx : y ≤ (1 + δ) * x + e) :
    |Real.exp (-x) - Real.exp (-y)| ≤
      16 * (δ + e) * Real.exp (-(y / 4)) := by
  have habs : |x - y| ≤ δ * y + e := by
    by_cases h : x ≤ y
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      have hmul : δ * x ≤ δ * y := mul_le_mul_of_nonneg_left h hδ
      linarith [hyx, hmul]
    · have hyx' : y ≤ x := le_of_not_ge h
      rw [abs_of_nonneg (sub_nonneg.mpr hyx')]
      linarith [hxy]
  have hminexp := exp_neg_min_le_three_mul hx hy hδ1 he1 hyx
  have hdiff := exp_neg_difference_le (x := x) (y := y)
  have hright : 0 ≤ δ * y + e := add_nonneg (mul_nonneg hδ hy) he
  have hmul_diff : |x - y| * Real.exp (-min x y) ≤
      (δ * y + e) * (3 * Real.exp (-(y / 2))) :=
    mul_le_mul habs hminexp (Real.exp_pos _).le hright
  have hyhalf := mul_exp_neg_half_le_four_mul_exp_neg_quarter (y := y)
  have hquarter := exp_neg_half_le_exp_neg_quarter hy
  have hδpart : 3 * (δ * (y * Real.exp (-(y / 2)))) ≤
      3 * (δ * (4 * Real.exp (-(y / 4)))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hyhalf hδ) (by positivity)
  have hepart : 3 * (e * Real.exp (-(y / 2))) ≤
      3 * (e * Real.exp (-(y / 4))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hquarter he) (by positivity)
  have hcoef : 12 * δ + 3 * e ≤ 16 * (δ + e) := by linarith
  have hcoefpart : (12 * δ + 3 * e) * Real.exp (-(y / 4)) ≤
      16 * (δ + e) * Real.exp (-(y / 4)) :=
    mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
  calc
    |Real.exp (-x) - Real.exp (-y)| ≤
        |x - y| * Real.exp (-min x y) := hdiff
    _ ≤ (δ * y + e) * (3 * Real.exp (-(y / 2))) := hmul_diff
    _ = 3 * (δ * (y * Real.exp (-(y / 2)))) +
        3 * (e * Real.exp (-(y / 2))) := by ring
    _ ≤ 3 * (δ * (4 * Real.exp (-(y / 4)))) +
        3 * (e * Real.exp (-(y / 4))) := add_le_add hδpart hepart
    _ = (12 * δ + 3 * e) * Real.exp (-(y / 4)) := by ring
    _ ≤ 16 * (δ + e) * Real.exp (-(y / 4)) := hcoefpart

end DifferentialGeometry.Analysis.Asymptotics
