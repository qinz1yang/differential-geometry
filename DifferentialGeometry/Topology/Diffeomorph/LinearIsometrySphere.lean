import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [Fact (Module.finrank ℝ F = n + 1)]

def sphereDiffeomorph (A : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : F) 1 where
  toFun x := ⟨A x.val, by
    rw [Metric.mem_sphere, dist_zero_right, A.norm_map]
    exact norm_eq_of_mem_sphere x⟩
  invFun x := ⟨A.symm x.val, by
    rw [Metric.mem_sphere, dist_zero_right, A.symm.norm_map]
    exact norm_eq_of_mem_sphere x⟩
  left_inv x := Subtype.ext (A.symm_apply_apply x.val)
  right_inv x := Subtype.ext (A.apply_symm_apply x.val)
  contMDiff_toFun := by
    apply ContMDiff.codRestrict_sphere
    exact A.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere
  contMDiff_invFun := by
    apply ContMDiff.codRestrict_sphere
    exact A.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere

theorem sphereDiffeomorph_apply (A : E ≃ₗᵢ[ℝ] F)
    (x : Metric.sphere (0 : E) 1) :
    (sphereDiffeomorph (n := n) A x).val = A x.val := rfl

theorem sphereDiffeomorph_symm_apply (A : E ≃ₗᵢ[ℝ] F)
    (x : Metric.sphere (0 : F) 1) :
    ((sphereDiffeomorph (n := n) A).symm x).val = A.symm x.val := rfl

end LinearIsometryEquiv
