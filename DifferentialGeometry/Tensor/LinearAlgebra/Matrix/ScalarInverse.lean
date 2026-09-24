import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]

theorem inv_smul_field (G : Matrix ι ι 𝕜) (c : 𝕜) :
    (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  by_cases hG : IsUnit G.det
  · let : Invertible c := invertibleOfNonzero hc
    simpa only [invOf_eq_inv] using Matrix.inv_smul G c hG
  · have hscaled : ¬IsUnit (c • G).det := by
      intro hs
      apply hG
      rw [Matrix.det_smul] at hs
      exact isUnit_of_mul_isUnit_right hs
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ hG, smul_zero]

end Matrix
