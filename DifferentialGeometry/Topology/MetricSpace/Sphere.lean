import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace Metric

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

theorem frontier_closedBall_eq_range_smul_linearIsometryEquiv
    (O : E ≃ₗᵢ[ℝ] F) {r : ℝ} (hr : 0 < r) :
    frontier (closedBall (0 : F) r) =
      Set.range (fun z : sphere (0 : E) 1 => r • O z.val) := by
  rw [frontier_closedBall (0 : F) hr.ne']
  ext x
  constructor
  · intro hx
    have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
    refine ⟨⟨O.symm (r⁻¹ • x), ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, O.symm.norm_map, norm_smul,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, hnorm, inv_mul_cancel₀ hr.ne']
    · simp only [O.apply_symm_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  · rintro ⟨z, rfl⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg hr.le,
      O.norm_map, mem_sphere_zero_iff_norm.mp z.property, mul_one]

end Metric
