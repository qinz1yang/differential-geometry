import Mathlib.Analysis.InnerProductSpace.Rayleigh

set_option autoImplicit false
open scoped InnerProductSpace
namespace DifferentialGeometry.Analysis

theorem opNorm_le_of_abs_inner_self_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : T.IsSymmetric) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : E, |⟪T x, x⟫_ℝ| ≤ C * ‖x‖ ^ 2) : ‖T‖ ≤ C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa only [hx, T.rayleighQuotient_apply_zero, abs_zero] using hC
  · have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      abs_div, abs_sq, div_le_iff₀ hn]
    exact hbound x

end DifferentialGeometry.Analysis
