import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Metric NormedSpace
namespace DifferentialGeometry.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isCoercive_of_pos_diagonal (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) : IsCoercive B := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl h =>
      let := h
      refine ⟨1, zero_lt_one, fun v => ?_⟩
      have hv : v = 0 := Subsingleton.elim _ _
      simp only [hv, norm_zero, mul_zero, map_zero, le_refl]
  | inr h =>
      let := h
      have hcont : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
      obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
      have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw1]; exact one_ne_zero)
      refine ⟨B w w, hB w hw0, fun v => ?_⟩
      by_cases hv : v = 0
      · simp only [hv, norm_zero, mul_zero, map_zero, le_refl]
      have hnorm : ‖normalize v‖ = 1 := norm_normalize hv
      have hbound : B w w ≤ B (normalize v) (normalize v) :=
        hmin (mem_sphere_zero_iff_norm.mpr hnorm)
      have hscale : B v v = ‖v‖ ^ 2 * B (normalize v) (normalize v) := by
        calc
          _ = B (‖v‖ • normalize v) (‖v‖ • normalize v) := by
            rw [norm_smul_normalize]
          _ = _ := by
            simp only [map_smul, smul_apply, smul_eq_mul]
            ring
      calc
        B w w * ‖v‖ * ‖v‖ = ‖v‖ ^ 2 * B w w := by ring
        _ ≤ ‖v‖ ^ 2 * B (normalize v) (normalize v) :=
          mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
        _ = B v v := hscale.symm

theorem exists_pos_radius_pos_diagonal (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : E →L[ℝ] E →L[ℝ] ℝ, ‖A - B‖ < δ →
      ∀ v : E, v ≠ 0 → 0 < A v v := by
  obtain ⟨c, hc, hcoerc⟩ := isCoercive_of_pos_diagonal B hB
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
