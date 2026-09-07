import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorRepresentation

set_option autoImplicit false

noncomputable section

namespace exteriorPower

open DifferentialGeometry.Geometry.Curvature
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem traceNormalizedCurvatureEndomorphism_pullback_eq_conjugate
    (e : E ≃ₗᵢ[ℝ] F)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    traceNormalizedCurvatureEndomorphism
      (T.compContinuousLinearMap (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap))
      (hT.compContinuousLinearMap e.toContinuousLinearEquiv.toContinuousLinearMap) =
      (mapLinearIsometryEquiv 2 e).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((traceNormalizedCurvatureEndomorphism T hT).comp
          (mapLinearIsometryEquiv 2 e).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply endomorphismTensor_injective 2
  ext v
  have hv : v = Fin.append ![v 0, v 1] ![v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, endomorphismTensor_apply_append, endomorphismTensor_apply_append]
  rw [inner_traceNormalizedCurvatureEndomorphism_ιMulti]
  change _ = ⟪(mapLinearIsometryEquiv 2 e).symm
    (traceNormalizedCurvatureEndomorphism T hT
      (mapLinearIsometryEquiv 2 e (ιMulti ℝ 2 ![v 0, v 1]))), ιMulti ℝ 2 ![v 2, v 3]⟫
  rw [(mapLinearIsometryEquiv 2 e).symm.inner_map_eq_flip]
  simp only [LinearIsometryEquiv.symm_symm, mapLinearIsometryEquiv_apply, map_apply_ιMulti]
  rw [inner_traceNormalizedCurvatureEndomorphism_ιMulti]
  congr 1
  change T (fun i => e (![v 0, v 1, v 3, v 2] i)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem traceNormalizedCurvatureEndomorphism_conjugate_inner_wedge
    (e : E ≃ₗᵢ[ℝ] F)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) (a b c d : E) :
    ⟪((mapLinearIsometryEquiv 2 e).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((traceNormalizedCurvatureEndomorphism T hT).comp
          (mapLinearIsometryEquiv 2 e).toContinuousLinearEquiv.toContinuousLinearMap))
        (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![c, d]⟫ =
      2 * T ![e a, e b, e d, e c] := by
  rw [← traceNormalizedCurvatureEndomorphism_pullback_eq_conjugate e T hT,
    inner_traceNormalizedCurvatureEndomorphism_ιMulti]
  congr 1
  change T (fun i => e (![a, b, d, c] i)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem traceNormalizedCurvatureEndomorphism_conjugate_isSelfAdjoint
    (e : E ≃ₗᵢ[ℝ] F)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    IsSelfAdjoint ((mapLinearIsometryEquiv 2 e).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((traceNormalizedCurvatureEndomorphism T hT).comp
        (mapLinearIsometryEquiv 2 e).toContinuousLinearEquiv.toContinuousLinearMap)) := by
  rw [← traceNormalizedCurvatureEndomorphism_pullback_eq_conjugate e T hT]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (traceNormalizedCurvatureEndomorphism_isSymmetric _ _)

end exteriorPower
