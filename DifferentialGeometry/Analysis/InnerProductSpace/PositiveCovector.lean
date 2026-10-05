import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Linarith

noncomputable section
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem apply_pos_of_near_unit_dual
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (l : E →L[ℝ] ℝ)
    (hsmall : ‖l - innerSL ℝ v‖ + ‖w - v‖ < 1) : 0 < l w := by
  have hdual : |l w - ⟪v, w⟫_ℝ| ≤ ‖l - innerSL ℝ v‖ := by
    simpa only [sub_apply, innerSL_apply_apply,
      Real.norm_eq_abs, hw, mul_one] using (l - innerSL ℝ v).le_opNorm w
  have hvector : |⟪v, w⟫_ℝ - 1| ≤ ‖w - v‖ := by
    have h := abs_real_inner_le_norm v (w - v)
    simpa only [inner_sub_right, real_inner_self_eq_norm_sq, hv, one_pow, one_mul] using h
  have hlo := (abs_le.mp hdual).1
  have hvl := (abs_le.mp hvector).1
  linarith

end DifferentialGeometry.Analysis
