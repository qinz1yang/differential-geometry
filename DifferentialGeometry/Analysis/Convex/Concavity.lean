import Mathlib.Analysis.Convex.Deriv

open Set

namespace DifferentialGeometry

theorem eq_of_concaveOn_univ_of_bddBelow
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f) (hbounded : BddBelow (range f))
    (x y : ℝ) : f x = f y := by
  obtain ⟨L, hL⟩ := hbounded
  have hlower (z : ℝ) : L ≤ f z := hL (mem_range_self z)
  have hle (u v : ℝ) : f u ≤ f v := by
    by_contra hnot
    have huv : f v < f u := lt_of_not_ge hnot
    let c : ℝ := f u - L + 1
    let a : ℝ := (f u - f v) / c
    have hc : 0 < c := by dsimp [c]; linarith [hlower u]
    have ha : 0 < a := div_pos (sub_pos.mpr huv) hc
    have ha_le : a ≤ 1 := by
      apply (div_le_one hc).mpr
      dsimp [c]
      linarith [hlower v]
    let z : ℝ := (v - (1 - a) * u) / a
    have hz : (1 - a) * u + a * z = v := by
      dsimp [z]
      field_simp [ne_of_gt ha]
      ring
    have hconc := hf.2 (mem_univ u) (mem_univ z)
      (sub_nonneg.mpr ha_le) ha.le (by ring : (1 - a) + a = 1)
    simp only [smul_eq_mul, hz] at hconc
    have hmul : a * c = f u - f v := by
      dsimp [a]
      exact div_mul_cancel₀ _ (ne_of_gt hc)
    have hlow := mul_le_mul_of_nonneg_left (hlower z) ha.le
    dsimp [c] at hmul
    nlinarith
  exact le_antisymm (hle x y) (hle y x)

theorem eq_of_deriv2_nonpos_of_bddBelow
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hdf : Differentiable ℝ (deriv f))
    (hsecond : ∀ t, deriv (deriv f) t ≤ 0)
    (hbounded : BddBelow (range f)) (x y : ℝ) : f x = f y := by
  apply eq_of_concaveOn_univ_of_bddBelow
    (concaveOn_univ_of_deriv2_nonpos hf hdf hsecond) hbounded

end DifferentialGeometry
