import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def equalRadiusStrainerMargin (r α : ℝ) : ℝ :=
  min (2 * r * (1 - Real.cos (α / 2)))
    (Real.sqrt 2 * r - 2 * r * Real.sin (Real.pi / 4 - α / 2))

theorem equalRadiusStrainerMargin_pos {r α : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1) :
    0 < equalRadiusStrainerMargin r α := by
  have hpi := Real.one_le_pi_div_two
  have hcos : Real.cos (α / 2) < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (by norm_num)
        (by linarith) (by linarith : 0 < α / 2)
  have hsin : Real.sin (Real.pi / 4 - α / 2) < Real.sqrt 2 / 2 := by
    rw [← Real.sin_pi_div_four]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith) (by linarith) (by linarith)
  have hcross : 0 < Real.sqrt 2 * r - 2 * r * Real.sin (Real.pi / 4 - α / 2) := by
    have hh := mul_lt_mul_of_pos_left hsin (show 0 < 2 * r by positivity)
    nlinarith
  exact lt_min (mul_pos (by positivity) (sub_pos.mpr hcos)) hcross

theorem comparisonAngle_eq_two_arcsin_of_equal_legs {r c : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hcr : c ≤ 2 * r) :
    comparisonAngle r r c = 2 * Real.arcsin (c / (2 * r)) := by
  have hnonneg : 0 ≤ c / (2 * r) := div_nonneg hc (by positivity)
  have hdiv : c / (2 * r) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith, (div_le_one₀ (by positivity)).mpr hcr⟩
  unfold comparisonAngle
  apply Real.arccos_eq_of_eq_cos (by linarith [Real.arcsin_nonneg.mpr hnonneg])
    (by linarith [Real.arcsin_le_pi_div_two (c / (2 * r))])
  rw [Real.cos_two_mul', Real.cos_sq', Real.sin_arcsin hdiv.1 hdiv.2]
  field_simp
  ring

theorem opposite_angle_of_equal_radius_chord_error {r α c D : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1)
    (hc : 0 ≤ c) (hcr : c ≤ 2 * r)
    (hD : D < equalRadiusStrainerMargin r α) (herror : |c - 2 * r| ≤ D) :
    0 < c ∧ Real.pi - α < comparisonAngle r r c := by
  have hpi := Real.one_le_pi_div_two
  have hD' := hD.trans_le (min_le_left (2 * r * (1 - Real.cos (α / 2)))
    (Real.sqrt 2 * r - 2 * r * Real.sin (Real.pi / 4 - α / 2)))
  have hchord : 2 * r * Real.cos (α / 2) < c := by
    have hh := (abs_le.mp herror).1
    linarith
  have hcos : 0 < Real.cos (α / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcpos : 0 < c := (mul_pos (by positivity) hcos).trans hchord
  refine ⟨hcpos, ?_⟩
  rw [comparisonAngle_eq_two_arcsin_of_equal_legs hr hc hcr]
  have hdiv : c / (2 * r) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [div_nonneg hc (show 0 ≤ 2 * r by positivity)],
      (div_le_one₀ (by positivity)).mpr hcr⟩
  have hs : Real.sin ((Real.pi - α) / 2) < c / (2 * r) := by
    rw [show (Real.pi - α) / 2 = Real.pi / 2 - α / 2 by ring,
      Real.sin_pi_div_two_sub]
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  have hh := (Real.lt_arcsin_iff_sin_lt
    (show (Real.pi - α) / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith, by linarith⟩) hdiv).mpr hs
  linarith

theorem cross_angle_of_equal_radius_chord_error {r α c D : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαone : α ≤ 1)
    (hc : 0 ≤ c) (hcr : c ≤ 2 * r)
    (hD : D < equalRadiusStrainerMargin r α)
    (herror : |c - Real.sqrt 2 * r| ≤ D) :
    0 < c ∧ Real.pi / 2 - α < comparisonAngle r r c := by
  have hpi := Real.one_le_pi_div_two
  have hD' := hD.trans_le (min_le_right (2 * r * (1 - Real.cos (α / 2)))
    (Real.sqrt 2 * r - 2 * r * Real.sin (Real.pi / 4 - α / 2)))
  have hchord : 2 * r * Real.sin (Real.pi / 4 - α / 2) < c := by
    have hh := (abs_le.mp herror).1
    linarith
  have hsin : 0 ≤ Real.sin (Real.pi / 4 - α / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hcpos : 0 < c := (mul_nonneg (by positivity) hsin).trans_lt hchord
  refine ⟨hcpos, ?_⟩
  rw [comparisonAngle_eq_two_arcsin_of_equal_legs hr hc hcr]
  have hdiv : c / (2 * r) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [div_nonneg hc (show 0 ≤ 2 * r by positivity)],
      (div_le_one₀ (by positivity)).mpr hcr⟩
  have hs : Real.sin (Real.pi / 4 - α / 2) < c / (2 * r) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  have hh := (Real.lt_arcsin_iff_sin_lt
    (show Real.pi / 4 - α / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith, by linarith⟩) hdiv).mpr hs
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
