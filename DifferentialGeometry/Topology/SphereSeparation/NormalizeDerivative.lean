import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Normalize

set_option autoImplicit false

open ContinuousLinearMap
open scoped RealInnerProductSpace

namespace Poincare.Topology.SphereSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def unitSphereTangentProjection (x : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ x).smulRight x

theorem hasFDerivAt_norm_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    HasFDerivAt (fun y : E => ‖y‖) (innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (by simp [hx])
  convert h using 1
  · funext y
    simp
  · simp only [norm_nonneg, Real.sqrt_sq, one_div, mul_inv_rev]
    rw [hx]
    ext y
    simp

theorem hasFDerivAt_normalize_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    HasFDerivAt (fun y : E => ‖y‖⁻¹ • y)
      (unitSphereTangentProjection x) x := by
  have hnorm := hasFDerivAt_norm_of_norm_eq_one hx
  have hinv := (hasFDerivAt_inv' (by simp [hx])).comp x hnorm
  have h := hinv.smul (hasFDerivAt_id x)
  have hderiv :
      (Inv.inv ∘ fun y : E => ‖y‖) x • ContinuousLinearMap.id ℝ E +
          ((-((ContinuousLinearMap.mulLeftRight ℝ ℝ) ‖x‖⁻¹) ‖x‖⁻¹) ∘L
            innerSL ℝ x).smulRight x =
        unitSphereTangentProjection x := by
    ext y
    simp only [unitSphereTangentProjection, Function.comp_apply,
      ContinuousLinearMap.neg_comp, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      neg_apply, sub_apply, ContinuousLinearMap.comp_apply,
      coe_innerSL_apply, ContinuousLinearMap.mulLeftRight_apply, neg_smul]
    rw [hx]
    simp only [inv_one, one_smul, one_mul, mul_one]
    change y + -(inner ℝ x y • x) = y - inner ℝ x y • x
    rw [sub_eq_add_neg]
  convert h using 1
  · funext y
    rfl
  · exact hderiv.symm

theorem fderiv_normalize_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    fderiv ℝ NormedSpace.normalize x = unitSphereTangentProjection x := by
  rw [show NormedSpace.normalize = (fun y : E => ‖y‖⁻¹ • y) by rfl]
  exact (hasFDerivAt_normalize_of_norm_eq_one hx).fderiv


theorem unitSphereTangentProjection_apply_self
    {x : E} (hx : ‖x‖ = 1) :
    unitSphereTangentProjection x x = 0 := by
  simp [unitSphereTangentProjection, hx]

theorem range_unitSphereTangentProjection
    {x : E} (hx : ‖x‖ = 1) :
    LinearMap.range (unitSphereTangentProjection x).toLinearMap =
      (ℝ ∙ x)ᗮ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change inner ℝ x (z - (inner ℝ x z) • x) = 0
    rw [inner_sub_right, inner_smul_right]
    rw [real_inner_self_eq_norm_sq, hx]
    simp
  · intro hy
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy
    refine ⟨y, ?_⟩
    simp [unitSphereTangentProjection, hy]

end Poincare.Topology.SphereSeparation
