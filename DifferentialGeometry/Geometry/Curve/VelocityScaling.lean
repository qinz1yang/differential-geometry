import DifferentialGeometry.Geometry.Curve.Reparametrization
import DifferentialGeometry.Bundle.TangentSpace

noncomputable section

namespace DifferentialGeometry.Geometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_comp_mul_apply_one
    (alpha : Real → M) (c : Real) (hc : c ≠ 0) (s : Real) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun r => alpha (c * r)) s) (1 : ℝ) =
      c • (mfderiv 𝓘(ℝ, ℝ) I alpha (c * s)) (1 : ℝ) := by
  by_cases halpha :
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (c * s)
  · let A : TangentSpace (modelWithCornersSelf Real Real) s →L[Real]
        TangentSpace (modelWithCornersSelf Real Real) (c * s) :=
      modelLinearMapToTangent
        (x := s) (y := c * s) (A := c • ContinuousLinearMap.id Real Real)
    have hscaleM : HasMFDerivAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) (fun r : Real => c * r) s A := by
      exact HasFDerivAt.hasMFDerivAt_model
        ((hasFDerivAt_id s).const_mul c)
    have hcomp := halpha.hasMFDerivAt.comp s hscaleM
    have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
    rw [tangentLinearMapToModel_comp] at hmodel
    have hA : tangentLinearMapToModel A =
        c • ContinuousLinearMap.id Real Real := by
      exact tangentLinearMapToModel_modelLinearMapToTangent
    rw [hA] at hmodel
    have happ := congrArg (fun L : Real →L[Real] E => L 1) hmodel
    have hfun : (alpha ∘ fun r : Real => c * r) =
        (fun r : Real => alpha (c * r)) := by
      rfl
    rw [hfun] at happ
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := I) (alpha (c * s))).injective
    simpa only [tangentLinearMapToModel_apply,
      tangentSpaceModelContinuousLinearEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Function.comp_apply, smul_apply, id_eq, map_smul] using happ
  · have hcomp : ¬MDifferentiableAt (modelWithCornersSelf Real Real) I
        (fun r => alpha (c * r)) s := by
      intro hcurve
      let beta : Real → M := fun r => alpha (c * r)
      have hcurve' : MDifferentiableAt (modelWithCornersSelf Real Real) I beta
          (c⁻¹ * (c * s)) := by
        simpa only [beta, inv_mul_cancel_left₀ hc] using hcurve
      have hinv : MDifferentiableAt (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) (fun r : Real => c⁻¹ * r) (c * s) := by
        exact mdifferentiableAt_iff_differentiableAt.mpr
          ((differentiableAt_const c⁻¹).mul differentiableAt_id)
      have hback := hcurve'.comp (c * s) hinv
      have heq : beta ∘ (fun r : Real => c⁻¹ * r) = alpha := by
        funext r
        simp only [beta, Function.comp_apply]
        field_simp [hc]
      rw [heq] at hback
      exact halpha hback
    simp only [mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt halpha]
    change (0 : E) = c • (0 : E)
    simp


end DifferentialGeometry.Geometry
