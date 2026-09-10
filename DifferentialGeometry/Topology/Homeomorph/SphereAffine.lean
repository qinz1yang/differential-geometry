import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

set_option autoImplicit false
noncomputable section
open Set Metric
namespace Poincare.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def sphereAffineHomeomorph (a : E) (r : ℝ) (hr : 0 < r) :
    sphere (0 : E) 1 ≃ₜ sphere a r :=
  ((Homeomorph.smulOfNeZero r hr.ne' : E ≃ₜ E).trans (Homeomorph.addLeft a)).subtype
    (fun v => by
      change v ∈ sphere (0 : E) 1 ↔ a + r • v ∈ sphere a r
      rw [mem_sphere_zero_iff_norm,mem_sphere,dist_eq_norm,
        add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.le]
      constructor <;> intro h
      · rw [h,mul_one]
      · nlinarith)


@[simp]
theorem sphereAffineHomeomorph_apply (a : E) (r : ℝ) (hr : 0 < r) (v : sphere (0 : E) 1) :
    (sphereAffineHomeomorph a r hr v : E) = a + r • v.val := rfl


@[simp]
theorem sphereAffineHomeomorph_symm_apply (a : E) (r : ℝ) (hr : 0 < r) (v : sphere a r) :
    ((sphereAffineHomeomorph a r hr).symm v : E) = r⁻¹ • (v.val-a) := by
  change (Homeomorph.smulOfNeZero r hr.ne').symm (-a + v.val) = _
  rw [Homeomorph.smulOfNeZero_symm_apply]
  congr 1
  abel
end Poincare.Topology
