import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicEstimates

set_option autoImplicit false

open Set

namespace Real

theorem sinh_le_self_mul_cosh {t R : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    sinh t ≤ t * cosh R := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_sinh x).hasDerivWithinAt)
    (fun x (hx : x ∈ Icc 0 t) => show ‖cosh x‖ ≤ cosh R from by
      rw [norm_eq_abs, abs_of_pos (cosh_pos x)]
      exact cosh_le_cosh.mpr (by rw [abs_of_nonneg hx.1, abs_of_nonneg (ht.trans htR)]; exact hx.2.trans htR))
    (convex_Icc 0 t) (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  simpa [norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg (sinh_nonneg_iff.mpr ht), mul_comm] using h

theorem cosh_sub_le_sinh_mul_sub {u v R : ℝ}
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

end Real
