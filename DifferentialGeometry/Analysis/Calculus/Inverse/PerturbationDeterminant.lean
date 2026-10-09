import DifferentialGeometry.Analysis.Calculus.Inverse.LipschitzPerturbationHomeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Analysis

theorem det_id_add_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℝ E + T).det ≠ 0 := by
  have hu : IsUnit ((idAddEquiv T hT : E ≃L[ℝ] E) : E →L[ℝ] E).det :=
    (idAddEquiv T hT).toLinearEquiv.isUnit_det'
  rw [coe_idAddEquiv] at hu
  exact hu.ne_zero

theorem det_id_add_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →L[ℝ] E) (hT : ‖T‖ < 1) :
    0 < (ContinuousLinearMap.id ℝ E + T).det := by
  have hcurve : Continuous fun t : ℝ => ContinuousLinearMap.id ℝ E + t • T := by fun_prop
  have hdet : Continuous fun A : E →L[ℝ] E => A.det := ContinuousLinearMap.continuous_det
  have hcont : ContinuousOn (fun t : ℝ => (ContinuousLinearMap.id ℝ E + t • T).det) (Icc 0 1) :=
    (hdet.comp hcurve).continuousOn
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (ContinuousLinearMap.id ℝ E + t • T).det ≠ 0 := by
    intro t ht
    have hle : ‖t • T‖ ≤ ‖T‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg T) ht.2
    exact det_id_add_ne_zero (t • T) (hle.trans_lt hT)
  have h0 : (ContinuousLinearMap.id ℝ E + (0 : ℝ) • T).det = 1 := by
    rw [zero_smul, add_zero]
    exact LinearMap.det_id
  have h1 : (ContinuousLinearMap.id ℝ E + (1 : ℝ) • T).det =
      (ContinuousLinearMap.id ℝ E + T).det := by
    rw [one_smul]
  by_contra hneg
  have hle : (ContinuousLinearMap.id ℝ E + (1 : ℝ) • T).det ≤ 0 := by
    rw [h1]
    exact not_lt.mp hneg
  have hmem : (0 : ℝ) ∈ Icc (ContinuousLinearMap.id ℝ E + (1 : ℝ) • T).det
      (ContinuousLinearMap.id ℝ E + (0 : ℝ) • T).det := by
    rw [h0]
    exact ⟨hle, zero_le_one⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  exact hne t ht hzero

theorem det_fderiv_lipschitzPerturbationHomeomorph_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (η : E → E) (hη : Differentiable ℝ η) {c : ℝ}
    (hc : c < 1) (hbound : ∀ x, ‖fderiv ℝ η x‖ ≤ c) (x : E) :
    0 < (fderiv ℝ ⇑(lipschitzPerturbationHomeomorph η hη hc hbound) x).det := by
  rw [fderiv_lipschitzPerturbationHomeomorph, coe_idAddEquiv]
  exact det_id_add_pos (fderiv ℝ η x) ((hbound x).trans_lt hc)

end DifferentialGeometry.Analysis
