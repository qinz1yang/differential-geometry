import DifferentialGeometry.Analysis.InnerProductSpace.PositiveInverseBounds
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped InnerProductSpace

namespace ConormalRegression

theorem identity_lower (x y : ℝ) :
    ‖x‖ ^ 2 - ‖y - x‖ * ‖x‖ ≤ ⟪x, y⟫_ℝ := by
  simpa using ContinuousLinearMap.inner_inverse_apply_lower_bound
    (1 : ℝ →L[ℝ] ℝ) ContinuousLinearMap.isPositive_one
    (a := 1) (b := 1) (by norm_num) (by norm_num)
    (by intro z; simp)
    (by intro z; simp) x y

theorem identity_dual_positive (β ξ : StrongDual ℝ ℝ)
    (hβ : 1 ≤ ‖β‖) (herr : ‖ξ - β‖ ≤ 1 / 2) :
    0 < β ((InnerProductSpace.toDual ℝ ℝ).symm ξ) := by
  simpa using ContinuousLinearMap.dual_apply_inverse_pos
    (1 : ℝ →L[ℝ] ℝ) ContinuousLinearMap.isPositive_one
    (δ := 0) (σ := 1 / 2) (m := 1) (by norm_num) (by norm_num)
    (by intro z; simp)
    (by intro z; simp) β ξ (by norm_num) hβ herr (by norm_num)

theorem strict_budget_boundary :
    let β := (InnerProductSpace.toDual ℝ ℝ) (1 : ℝ)
    let ξ := (0 : StrongDual ℝ ℝ)
    ‖β‖ = 1 ∧ ‖ξ - β‖ = 1 ∧
      β ((Ring.inverse (1 : ℝ →L[ℝ] ℝ)) ((InnerProductSpace.toDual ℝ ℝ).symm ξ)) = 0 := by
  simp

#print axioms identity_lower
#print axioms identity_dual_positive
#print axioms strict_budget_boundary
end ConormalRegression
