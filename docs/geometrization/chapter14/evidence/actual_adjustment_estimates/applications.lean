import DifferentialGeometry.Analysis.Calculus.PerturbedProjection
import DifferentialGeometry.Analysis.Calculus.CutoffAdjustment
import DifferentialGeometry.Analysis.Calculus.AdjustmentProjections
import DifferentialGeometry.Analysis.InnerProductSpace.SubspaceRankTransfer
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric DifferentialGeometry.Analysis

namespace AdjustmentRegression

private noncomputable def doubleMap : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

theorem nonzero_cutoff_chain_factor :
    ‖fderiv ℝ (fun y : ℝ => doubleMap y + doubleMap y * (doubleMap y + 1 / 10 - doubleMap y))
      (1 / 4) - fderiv ℝ doubleMap (1 / 4)‖ ≤ 1 / 5 := by
  have hh := projected_cutoff_adjustment_value_derivative_le
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
    (f := doubleMap) (ψ := id) (P := fun z : ℝ => z + 1 / 10) (x := 1 / 4)
    (a := 1 / 10) (b := 1) (L := 2) (d := 0) (e := 0) (ρ := 1)
    (by simp) (by simp) doubleMap.differentiableAt differentiableAt_id
    (differentiableAt_id.add_const _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [doubleMap]) (by norm_num) (by simp)
    (by rw [doubleMap.hasFDerivAt.fderiv]; simp only [doubleMap, norm_smul]; norm_num)
    (by simp)
    (by simp)
  convert hh.2 using 1 <;> norm_num [smul_eq_mul]

theorem original_half_tube_and_projection {P : ℝ → ℝ}
    (hP : ∀ z ∈ ball (0 : ℝ) 1, DifferentiableAt ℝ P z)
    (hderiv : ∀ z ∈ ball (0 : ℝ) 1, ‖fderiv ℝ P z - ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 / 100)
    (hbase : ‖P 0‖ ≤ 1 / 100) :
    ball (1 / 10 : ℝ) (1 / 2) ⊆ ball (0 : ℝ) 1 ∧
      segment ℝ (0 : ℝ) (1 / 10) ⊆ ball (0 : ℝ) 1 ∧
      ‖P (1 / 10) - 1 / 10‖ ≤ (5 / 3 : ℝ) * (1 / 100) + (1 + 1 / 100) * (1 / 10) := by
  have hh := perturbed_projection_on_original_ball (x := (0 : ℝ)) (y := 1 / 10)
    (ρ := 1) (σ := 1) (r := 1) (ε := 1 / 100) (e := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (ContinuousLinearMap.id ℝ ℝ) (by simp) hP hderiv
    (by simpa only [sub_zero, mul_one] using hbase)
  simpa only [mul_one] using hh.2

theorem actual_second_coordinate_retained (ψ : ℝ × ℝ → ℝ) (v : ℝ × ℝ → ℝ)
    (x : ℝ × ℝ) :
    (x + ψ x • (v x, (0 : ℝ))).2 = x.2 := by
  let J : ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.id ℝ ℝ).prod 0
  have hh := retained_projection_cutoff_adjustment (ContinuousLinearMap.snd ℝ ℝ ℝ) J
    (by ext; simp [J]) ψ v
  exact congrFun hh x

theorem kernel_inclusion_can_be_strict :
    (fderiv ℝ (id : ℝ → ℝ) 0).ker ≠ (fderiv ℝ ((fun _ : ℝ => (0 : ℝ)) ∘ id) 0).ker := by
  intro h
  have hh : (1 : ℝ) ∈ (fderiv ℝ ((fun _ : ℝ => (0 : ℝ)) ∘ id) 0).ker := by
    simp
  rw [← h] at hh
  simp at hh

theorem zero_rank_cannot_fill_positive_target :
    ¬ Module.finrank ℝ (⊤ : Submodule ℝ ℝ) ≤
      Module.finrank ℝ (0 : ℝ →L[ℝ] ℝ).range := by
  simp

theorem perturbed_identity_onto_original_target :
    Function.Surjective (((3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ).codRestrict
      (⊤ : Submodule ℝ ℝ) (fun _ => Submodule.mem_top)) := by
  apply ContinuousLinearMap.surjective_codRestrict_of_rank_margin
    (ContinuousLinearMap.id ℝ ℝ) ((3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (⊤ : Submodule ℝ ℝ) (fun _ => Submodule.mem_top) (μ := 1) (δ := 1 / 4)
  · norm_num
  · have heq : (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ - ContinuousLinearMap.id ℝ ℝ =
        (-1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by module
    rw [heq, norm_smul]
    norm_num
  · intro v hv
    simp
  · rw [show (ContinuousLinearMap.id ℝ ℝ).range = ⊤ from
      LinearMap.range_eq_top.mpr Function.surjective_id]

theorem nonzero_prior_error_in_actual_adjustment :
    let g : ℝ → ℝ := fun y => doubleMap y + doubleMap y * (doubleMap y + 1 / 10 - doubleMap y)
    ‖g (1 / 4) - (1 / 4)‖ ≤ 7 / 20 ∧
      ‖fderiv ℝ g (1 / 4) - fderiv ℝ (id : ℝ → ℝ) (1 / 4)‖ ≤ 11 / 5 := by
  have hh := projected_cutoff_adjustment_cumulative_le
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
    (f := doubleMap) (f₀ := id) (ψ := id) (P := fun z : ℝ => z + 1 / 10) (x := 1 / 4)
    (a := 1 / 10) (b := 1) (L := 1) (d := 0) (ν := 0) (ρ := 1) (E₀ := 1 / 4) (H₀ := 1)
    (by simp) (by simp) (by simp) doubleMap.differentiableAt differentiableAt_id
    (differentiableAt_id.add_const _) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [doubleMap]) (by norm_num) (by simp)
    (by simp) (by simp) (by simp) (by norm_num [doubleMap])
    (by
      rw [doubleMap.hasFDerivAt.fderiv, fderiv_id]
      have heq : doubleMap - ContinuousLinearMap.id ℝ ℝ = ContinuousLinearMap.id ℝ ℝ := by
        dsimp [doubleMap]
        module
      rw [heq]
      norm_num)
  convert hh using 1
  norm_num [smul_eq_mul]

end AdjustmentRegression

#print axioms AdjustmentRegression.nonzero_cutoff_chain_factor

#print axioms AdjustmentRegression.original_half_tube_and_projection

#print axioms AdjustmentRegression.actual_second_coordinate_retained

#print axioms AdjustmentRegression.kernel_inclusion_can_be_strict

#print axioms AdjustmentRegression.zero_rank_cannot_fill_positive_target

#print axioms AdjustmentRegression.perturbed_identity_onto_original_target

#print axioms AdjustmentRegression.nonzero_prior_error_in_actual_adjustment
