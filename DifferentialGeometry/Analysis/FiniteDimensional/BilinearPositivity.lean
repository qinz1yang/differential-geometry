import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Metric NormedSpace
namespace DifferentialGeometry.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_pos_radius_pos_diagonal (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : E →L[ℝ] E →L[ℝ] ℝ, ‖A - B‖ < δ →
      ∀ v : E, v ≠ 0 → 0 < A v v := by
  obtain ⟨c, hc, hcoerc⟩ := B.isCoercive_of_posDef hB
  refine ⟨c, hc, fun A hA v hv => ?_⟩
  have herr : |A v v - B v v| ≤ ‖A - B‖ * ‖v‖ * ‖v‖ := by
    simpa only [sub_apply, Real.norm_eq_abs] using
      (A - B).le_opNorm₂ v v
  have hstrict : ‖A - B‖ * ‖v‖ * ‖v‖ < c * ‖v‖ * ‖v‖ :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hA (norm_pos_iff.mpr hv))
      (norm_pos_iff.mpr hv)
  have habs := (abs_le.mp herr).1
  linarith [hcoerc v]

theorem isOpen_pos_diagonal :
    IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ v : E, v ≠ 0 → 0 < B v v} := by
  apply (Metric.isOpen_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).mpr
  intro B hB
  obtain ⟨δ, hδ, hball⟩ := exists_pos_radius_pos_diagonal B hB
  refine ⟨δ, hδ, fun A hA => ?_⟩
  apply hball A
  change dist A B < δ at hA
  rw [dist_eq_norm A B] at hA
  exact hA

end DifferentialGeometry.Analysis
