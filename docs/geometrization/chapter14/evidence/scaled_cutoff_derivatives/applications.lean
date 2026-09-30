import DifferentialGeometry.Analysis.Calculus.ScaledCutoffBlock
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open DifferentialGeometry.Analysis Set Metric

namespace ScaledCutoffRegression

private def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

theorem nonzero_block_and_far_exterior :
    scaledCutoffBlock 2 bump 1 = WithLp.toLp 2 ((1 : ℝ), (2 : ℝ)) ∧
    scaledCutoffBlock 2 bump 10000 = 0 := by
  have h1 : bump ((2 : ℝ)⁻¹) = 1 := bump.one_of_mem_closedBall (by norm_num [bump])
  have h2 : bump (2⁻¹ * (10000 : ℝ)) = 0 := bump.zero_of_le_dist (by norm_num [bump])
  simp only [scaledCutoffBlock, smul_eq_mul, mul_one, h1, h2, zero_mul, mul_zero]
  exact ⟨trivial, rfl⟩

theorem actual_bump_derivative_bounds_exist :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ x, ‖fderiv ℝ bump x‖ ≤ A) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ bump) x‖ ≤ B) := by
  have hD : ContDiff ℝ 2 (fderiv ℝ bump) :=
    (bump.contDiff : ContDiff ℝ 3 bump).fderiv_right (by norm_num)
  have hDD : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ bump)) := hD.fderiv_right (by norm_num)
  obtain ⟨A, hA⟩ := hD.continuous.norm.bddAbove_range_of_hasCompactSupport
    (bump.hasCompactSupport.fderiv ℝ |>.comp_left norm_zero)
  obtain ⟨B, hB⟩ := hDD.continuous.norm.bddAbove_range_of_hasCompactSupport
    ((bump.hasCompactSupport.fderiv ℝ).fderiv ℝ |>.comp_left norm_zero)
  refine ⟨A, B, (norm_nonneg _).trans (hA (mem_range_self 0)),
    (norm_nonneg _).trans (hB (mem_range_self 0)), ?_, ?_⟩
  · exact fun x => hA (mem_range_self x)
  · exact fun x => hB (mem_range_self x)

theorem same_nonzero_cutoff_at_two_scales :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ x, ‖fderiv ℝ (scaledCutoffBlock 2 bump) x‖ ≤ 1 + 3 * A ∧
        ‖fderiv ℝ (fderiv ℝ (scaledCutoffBlock 2 bump)) x‖ ≤ (2 * A + 3 * B) / 2) ∧
      (∀ x, ‖fderiv ℝ (scaledCutoffBlock 4 bump) x‖ ≤ 1 + 3 * A ∧
        ‖fderiv ℝ (fderiv ℝ (scaledCutoffBlock 4 bump)) x‖ ≤ (2 * A + 3 * B) / 4) := by
  obtain ⟨A, B, hA, hB, hD, hDD⟩ := actual_bump_derivative_bounds_exist
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro x
    simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using
      scaledCutoffBlock_derivative_bounds bump.contDiff (s := 2) (C := 2)
        (by norm_num) (by norm_num) hA hB (fun _ => ⟨bump.nonneg, bump.le_one⟩)
        (by rw [bump.tsupport_eq]; exact Subset.rfl) hD hDD x
  · intro x
    simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using
      scaledCutoffBlock_derivative_bounds bump.contDiff (s := 4) (C := 2)
        (by norm_num) (by norm_num) hA hB (fun _ => ⟨bump.nonneg, bump.le_one⟩)
        (by rw [bump.tsupport_eq]; exact Subset.rfl) hD hDD x

theorem both_product_cross_terms (x : ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fun y : ℝ => y * y)) x‖ ≤ 2 := by
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hi : fderiv ℝ (id : ℝ → ℝ) = fun _ => ContinuousLinearMap.id ℝ ℝ :=
    funext fun y => (hasFDerivAt_id y).fderiv
  have hh := B.norm_second_fderiv_bilinear_le (f := id) (g := id)
    differentiable_id differentiable_id
    (by rw [hi]; exact differentiableAt_const _)
    (by rw [hi]; exact differentiableAt_const _) (x := x)
  rw [hi] at hh
  simpa [B, ContinuousLinearMap.opNorm_lsmul, smul_eq_mul] using hh

theorem original_composition_with_unbounded_translation :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ x : ℝ,
      max ‖scaledCutoffBlock 2 bump (x + 10000) - scaledCutoffBlock 2 bump (x + 10001)‖
        ‖fderiv ℝ (scaledCutoffBlock 2 bump ∘ (fun y : ℝ => y + 10000)) x -
          fderiv ℝ (scaledCutoffBlock 2 bump ∘ (fun y : ℝ => y + 10001)) x‖ ≤
        1 + 3 * A + (2 * A + 3 * B) / 2 := by
  obtain ⟨A, B, hA, hB, hD, hDD⟩ := actual_bump_derivative_bounds_exist
  refine ⟨A, B, hA, hB, fun x => ?_⟩
  have hh := scaledCutoffBlock_c1_comp_sub_le bump.contDiff (s := 2) (C := 2)
    (by norm_num) (by norm_num) hA hB (fun _ => ⟨bump.nonneg, bump.le_one⟩)
    (by rw [bump.tsupport_eq]; exact Subset.rfl) hD hDD
    (U := fun y : ℝ => y + 10000) (V := fun y : ℝ => y + 10001) (x := x)
    (differentiableAt_id.add_const _) (differentiableAt_id.add_const _)
    (ε := 1) (L := 1) (by norm_num) (by norm_num)
    (by ring_nf; norm_num) (by simp) (by simp)
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num, mul_one] using hh

end ScaledCutoffRegression

#print axioms ScaledCutoffRegression.nonzero_block_and_far_exterior
#print axioms ScaledCutoffRegression.actual_bump_derivative_bounds_exist
#print axioms ScaledCutoffRegression.same_nonzero_cutoff_at_two_scales
#print axioms ScaledCutoffRegression.both_product_cross_terms
#print axioms ScaledCutoffRegression.original_composition_with_unbounded_translation
