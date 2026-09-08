import DifferentialGeometry.Geometry.LieGroup.Orthogonal
import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Bundle.PartialMfderiv.Composition
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

theorem mvfderiv_symm_apply_one
    (U : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) (E ≃ₗᵢ[ℝ] E))
    (w : E) :
    mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))
      (fun g : E ≃ₗᵢ[ℝ] E => g.symm w) 1 U = -(groupLieAlgebraEquiv U : E →L[ℝ] E) w := by
  have hA := (contMDiff_toContinuousLinearMap (E := E) (n := 1) 1).mdifferentiableAt (by simp)
  have hi : ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) 𝓘(ℝ, E →L[ℝ] E) 1
      (fun g : E ≃ₗᵢ[ℝ] E => (g.symm : E →L[ℝ] E)) :=
    contMDiff_iff.mp contMDiff_id.inv
  have hv := (hi.clm_apply (contMDiff_const (c := w)) 1).mdifferentiableAt (by simp)
  have hd := congrArg (fun L => L U) (hA.mvfderiv_clm_apply hv)
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, mvfderiv_const, zero_apply] at hd
  have heq := coe_groupLieAlgebraEquiv (E := E) U
  have h := congrArg (fun L : E →L[ℝ] E => L w) heq
  change (groupLieAlgebraEquiv U : E →L[ℝ] E) w = _ at h
  change 0 = mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))
      (fun g : E ≃ₗᵢ[ℝ] E => g.symm w) 1 U +
    mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))
      (fun g : E ≃ₗᵢ[ℝ] E => (g : E →L[ℝ] E)) 1 U w at hd
  rw [← h] at hd
  exact eq_neg_of_add_eq_zero_left hd.symm

end LinearIsometryEquiv
