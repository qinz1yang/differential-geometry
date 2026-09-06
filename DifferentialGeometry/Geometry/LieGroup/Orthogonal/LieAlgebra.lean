import DifferentialGeometry.Geometry.LieGroup.Orthogonal
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.GroupLieAlgebra

noncomputable section

open scoped Manifold

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem cayleyChartAt_self (p : E ≃ₗᵢ[ℝ] E) : cayleyChartAt p p = 0 := by
  have h := (cayleyChartAt p).right_inv (show (0 : skewAdjoint.submodule ℝ (E →L[ℝ] E)) ∈
    (cayleyChartAt p).target by simp)
  rw [cayleyChartAt_symm_apply] at h
  have hz : skewAdjoint.cayleyTransform
      (0 : skewAdjoint.submodule ℝ (E →L[ℝ] E)) = (1 : E ≃ₗᵢ[ℝ] E) :=
    skewAdjoint.cayleyTransform_zero
  rwa [hz, mul_one] at h

def groupLieAlgebraEquiv :
    GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) (E ≃ₗᵢ[ℝ] E) ≃L[ℝ]
      skewAdjoint.submodule ℝ (E →L[ℝ] E) :=
  (DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))) (1 : E ≃ₗᵢ[ℝ] E)).trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
      (Units.mk0 (-2 : ℝ) (by norm_num)))

theorem groupLieAlgebraEquiv_apply
    (v : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) (E ≃ₗᵢ[ℝ] E)) :
    groupLieAlgebraEquiv v = (-2 : ℝ) •
      DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))) (1 : E ≃ₗᵢ[ℝ] E) v := rfl

theorem hasMFDerivAt_toContinuousLinearMap_one :
    HasMFDerivAt 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) 𝓘(ℝ, E →L[ℝ] E)
      (fun p : E ≃ₗᵢ[ℝ] E => (p : E →L[ℝ] E)) 1
      ((skewAdjoint.submodule ℝ (E →L[ℝ] E)).subtypeL.comp
        groupLieAlgebraEquiv.toContinuousLinearMap) := by
  refine ⟨continuous_toContinuousLinearMap.continuousAt, ?_⟩
  have h := (skewAdjoint.hasFDerivAt_cayleyTransform_toContinuousLinearMap_zero
    (E := E)).hasFDerivWithinAt (s := Set.univ)
  change HasFDerivWithinAt
    (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
      ((cayleyChartAt (1 : E ≃ₗᵢ[ℝ] E)).symm K : E →L[ℝ] E)) _
    (Set.range id) (cayleyChartAt (1 : E ≃ₗᵢ[ℝ] E) 1)
  rw [Set.range_id, cayleyChartAt_self]
  convert! h using 1

theorem mvfderiv_toContinuousLinearMap_one :
    mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))
      (fun p : E ≃ₗᵢ[ℝ] E => (p : E →L[ℝ] E)) 1 =
      (skewAdjoint.submodule ℝ (E →L[ℝ] E)).subtypeL.comp
        groupLieAlgebraEquiv.toContinuousLinearMap := by
  unfold mvfderiv
  rw [hasMFDerivAt_toContinuousLinearMap_one.mfderiv]
  rfl

theorem coe_groupLieAlgebraEquiv
    (v : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) (E ≃ₗᵢ[ℝ] E)) :
    (groupLieAlgebraEquiv v : E →L[ℝ] E) =
      mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))
        (fun p : E ≃ₗᵢ[ℝ] E => (p : E →L[ℝ] E)) 1 v := by
  rw [mvfderiv_toContinuousLinearMap_one]
  rfl

end LinearIsometryEquiv
