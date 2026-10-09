import DifferentialGeometry.Geometry.Comparison.ModelAngleFiniteDifference

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem cosh_sub_le_sinh_mul_sub {u v R : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ R) :
    cosh v - cosh u ≤ sinh R * (v - u) := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_cosh x).hasDerivWithinAt)
    (fun x (hx : x ∈ Icc u v) => show ‖sinh x‖ ≤ sinh R from by
      rw [norm_eq_abs, abs_of_nonneg (sinh_nonneg_iff.mpr (hu.trans hx.1))]
      exact sinh_le_sinh.mpr (hx.2.trans hv))
    (convex_Icc u v) (show u ∈ Icc u v from ⟨le_rfl, huv⟩)
    (show v ∈ Icc u v from ⟨huv, le_rfl⟩)
  rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at h
  exact (le_abs_self _).trans h

theorem comparisonAngles_of_small_triangle_excess
    {a A r t s η δ : ℝ} (ha : 0 < a) (har : a ≤ r) (hrA : r ≤ A)
    (ht : 0 < t) (ht1 : t ≤ 1) (hta : t ≤ a / 2)
    (hηt : η ≤ t) (hs : r - t ≤ s) (hsη : s ≤ r - t + η)
    (hδ : 0 ≤ δ)
    (hbudget : sinh (A + 1) * η ≤ (1 - cos δ) * (sinh (a / 2) * t)) :
    Real.pi - δ ≤ comparisonAngleNegCurvature 1 s t r ∧
      comparisonAngleNegCurvature 1 r t s ≤ δ := by
  have hr : 0 < r := ha.trans_le har
  have hsbound : a / 2 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hsr : s ≤ r := by linarith
  have hst : t ≤ s := by linarith
  have hrt : t ≤ r := by linarith
  have hR : 0 < A + 1 := by linarith
  have hsinht : 0 < sinh t := sinh_pos_iff.mpr ht
  have hsinhs : 0 < sinh s := sinh_pos_iff.mpr hs0
  have hsinhr : 0 < sinh r := sinh_pos_iff.mpr hr
  have hsinhtlo : t ≤ sinh t := self_le_sinh_iff.mpr ht.le
  have hδcos : 0 ≤ 1 - cos δ := sub_nonneg.mpr (cos_le_one δ)
  have hds : sinh (a / 2) * t ≤ sinh s * sinh t :=
    mul_le_mul (sinh_le_sinh.mpr hsbound) hsinhtlo ht.le hsinhs.le
  have hdr : sinh (a / 2) * t ≤ sinh r * sinh t :=
    mul_le_mul (sinh_le_sinh.mpr (by linarith)) hsinhtlo ht.le hsinhr.le
  have hcos1 : cos (comparisonAngleNegCurvature 1 s t r) =
      (cosh s * cosh t - cosh r) / (sinh s * sinh t) := by
    simpa using cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1)
      hs0 ht (by rw [abs_of_nonneg (sub_nonneg.mpr hst)]; linarith) (by linarith)
  have hcos2 : cos (comparisonAngleNegCurvature 1 r t s) =
      (cosh r * cosh t - cosh s) / (sinh r * sinh t) := by
    simpa using cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1)
      hr ht (by rw [abs_of_nonneg (sub_nonneg.mpr hrt)]; exact hs) (by linarith)
  have hid1 := (eq_div_iff (mul_pos hsinhs hsinht).ne').mp hcos1
  have hid2 := (eq_div_iff (mul_pos hsinhr hsinht).ne').mp hcos2
  have hnum1 : cosh (s + t) - cosh r ≤ sinh (A + 1) * η := by
    have h := cosh_sub_le_sinh_mul_sub hr.le (by linarith : r ≤ s + t)
      (show s + t ≤ A + 1 by linarith)
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (sinh_pos_iff.mpr hR).le)
  have hnum2 : cosh s - cosh (r - t) ≤ sinh (A + 1) * η := by
    have h := cosh_sub_le_sinh_mul_sub (sub_nonneg.mpr hrt) hs (show s ≤ A + 1 by linarith)
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (sinh_pos_iff.mpr hR).le)
  rw [cosh_add] at hnum1
  rw [cosh_sub] at hnum2
  have hang1 : cos (comparisonAngleNegCurvature 1 s t r) ≤ cos (Real.pi - δ) := by
    rw [cos_pi_sub]
    have hb := hbudget.trans (mul_le_mul_of_nonneg_left hds hδcos)
    apply (mul_le_mul_iff_right₀ (mul_pos hsinhs hsinht)).mp
    nlinarith only [hid1, hnum1, hb]
  have hang2 : cos δ ≤ cos (comparisonAngleNegCurvature 1 r t s) := by
    have hb := hbudget.trans (mul_le_mul_of_nonneg_left hdr hδcos)
    apply (mul_le_mul_iff_right₀ (mul_pos hsinhr hsinht)).mp
    nlinarith only [hid2, hnum2, hb]
  constructor
  · by_contra h
    have hlt := cos_lt_cos_of_nonneg_of_le_pi
      (comparisonAngleNegCurvature_mem_Icc 1 s t r).1
      (show Real.pi - δ ≤ Real.pi by linarith) (lt_of_not_ge h)
    exact (not_lt_of_ge hang1) hlt
  · by_contra h
    have hlt := cos_lt_cos_of_nonneg_of_le_pi hδ
      (comparisonAngleNegCurvature_mem_Icc 1 r t s).2 (lt_of_not_ge h)
    exact (not_lt_of_ge hang2) hlt

end DifferentialGeometry.Geometry.Comparison.Toponogov
