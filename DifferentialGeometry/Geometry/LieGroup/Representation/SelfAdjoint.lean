import DifferentialGeometry.Geometry.LieGroup.Orthogonal
import Mathlib.RepresentationTheory.Continuous.Basic

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

private local instance selfAdjointNormedAddCommGroup : NormedAddCommGroup (selfAdjoint.submodule ℝ (W →L[ℝ] W)) :=
  (selfAdjoint.submodule ℝ (W →L[ℝ] W)).normedAddCommGroup
private local instance selfAdjointNormedSpace : NormedSpace ℝ (selfAdjoint.submodule ℝ (W →L[ℝ] W)) :=
  (selfAdjoint.submodule ℝ (W →L[ℝ] W)).normedSpace

private def orthogonalConjugationCLM (e : W ≃ₗᵢ[ℝ] W) : (W →L[ℝ] W) →L[ℝ] (W →L[ℝ] W) :=
  e.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap

private theorem orthogonalConjugation_mem_selfAdjoint (e : W ≃ₗᵢ[ℝ] W)
    (A : selfAdjoint.submodule ℝ (W →L[ℝ] W)) :
    orthogonalConjugationCLM e (A : W →L[ℝ] W) ∈ selfAdjoint.submodule ℝ (W →L[ℝ] W) := by
  exact IsSelfAdjoint.map A.property e.conjStarAlgEquiv

private def orthogonalConjugation (e : W ≃ₗᵢ[ℝ] W) :
    (selfAdjoint.submodule ℝ (W →L[ℝ] W)) →L[ℝ]
      selfAdjoint.submodule ℝ (W →L[ℝ] W) :=
  ((orthogonalConjugationCLM e).comp (selfAdjoint.submodule ℝ (W →L[ℝ] W)).subtypeL).codRestrict
    (selfAdjoint.submodule ℝ (W →L[ℝ] W)) (fun A => orthogonalConjugation_mem_selfAdjoint e A)

def selfAdjointConjugation :
    ContRepresentation ℝ (W ≃ₗᵢ[ℝ] W) (selfAdjoint.submodule ℝ (W →L[ℝ] W)) :=
  .ofMonoidHom {
    toFun := orthogonalConjugation
    map_one' := by
      ext A x
      rfl
    map_mul' := by
      intro e f
      ext A x
      rfl
  }

@[simp]
theorem selfAdjointConjugation_apply (e : W ≃ₗᵢ[ℝ] W)
    (A : selfAdjoint.submodule ℝ (W →L[ℝ] W)) :
    selfAdjointConjugation e A =
      ⟨e.conjStarAlgEquiv (A : W →L[ℝ] W), A.property.map e.conjStarAlgEquiv⟩ := rfl

private def selfAdjointPartCLM :
    (W →L[ℝ] W) →L[ℝ] selfAdjoint.submodule ℝ (W →L[ℝ] W) where
  __ := selfAdjointPart ℝ
  cont := by
    apply continuous_induced_rng.mpr
    exact (continuous_id.add continuous_star).const_smul (⅟ (2 : ℝ))

private theorem selfAdjointPartCLM_apply (A : selfAdjoint.submodule ℝ (W →L[ℝ] W)) :
    selfAdjointPartCLM (A : W →L[ℝ] W) = A :=
  LinearMap.congr_fun
    (selfAdjointPart_comp_subtype_selfAdjoint (R := ℝ) (A := W →L[ℝ] W)) A

private theorem contMDiff_orthogonalConjugationCLM {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
      𝓘(ℝ, (W →L[ℝ] W) →L[ℝ] W →L[ℝ] W) n
      (orthogonalConjugationCLM (W := W)) := by
  have hf := LinearIsometryEquiv.contMDiff_toContinuousLinearMap (E := W) (n := n)
  have hi : ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
      𝓘(ℝ, W →L[ℝ] W) n (fun p : W ≃ₗᵢ[ℝ] W => ((p⁻¹ : W ≃ₗᵢ[ℝ] W) : W →L[ℝ] W)) :=
    hf.comp (contMDiff_inv _ n)
  have h := (hi.clm_precomp (F₃ := W)).clm_comp (hf.clm_postcomp (F₁ := W))
  exact h.congr fun p => by ext A x; rfl

private theorem contMDiff_orthogonalConjugation {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
      𝓘(ℝ, (selfAdjoint.submodule ℝ (W →L[ℝ] W)) →L[ℝ]
        selfAdjoint.submodule ℝ (W →L[ℝ] W)) n (orthogonalConjugation (W := W)) := by
  have h := (contMDiff_const (c := selfAdjointPartCLM (W := W))).clm_comp
    ((contMDiff_orthogonalConjugationCLM (W := W) (n := n)).clm_comp
      (contMDiff_const (c := (selfAdjoint.submodule ℝ (W →L[ℝ] W)).subtypeL)))
  apply h.congr
  intro p
  apply ContinuousLinearMap.ext
  intro A
  exact (selfAdjointPartCLM_apply (orthogonalConjugation p A)).symm

theorem contMDiff_selfAdjointConjugation {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
      𝓘(ℝ, (selfAdjoint.submodule ℝ (W →L[ℝ] W)) →L[ℝ]
        selfAdjoint.submodule ℝ (W →L[ℝ] W)) n
      (fun p : W ≃ₗᵢ[ℝ] W => selfAdjointConjugation p) :=
  contMDiff_orthogonalConjugation

end ContRepresentation
