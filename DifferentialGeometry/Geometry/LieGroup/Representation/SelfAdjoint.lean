import DifferentialGeometry.Geometry.LieGroup.Orthogonal.LieAlgebra
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

private theorem mvfderiv_conjugation_one_apply
    (U : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W)) (W ≃ₗᵢ[ℝ] W))
    (A : W →L[ℝ] W) (w : W) :
    mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
      (fun g : W ≃ₗᵢ[ℝ] W => g (A (g.symm w))) 1 U =
      (LinearIsometryEquiv.groupLieAlgebraEquiv U : W →L[ℝ] W) (A w) -
        A ((LinearIsometryEquiv.groupLieAlgebraEquiv U : W →L[ℝ] W) w) := by
  let O := 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
  have hbase := (LinearIsometryEquiv.contMDiff_toContinuousLinearMap (E := W) (n := 1)
    (1 : W ≃ₗᵢ[ℝ] W)).mdifferentiableAt (by simp)
  have hi : ContMDiff O 𝓘(ℝ, W →L[ℝ] W) 1
      (fun g : W ≃ₗᵢ[ℝ] W => (g.symm : W →L[ℝ] W)) :=
    LinearIsometryEquiv.contMDiff_iff.mp contMDiff_id.inv
  have hw := (hi.clm_apply (contMDiff_const (c := w)) 1).mdifferentiableAt (by simp)
  have hAw := (mdifferentiableAt_const (c := (A : W →L[ℝ] W))).clm_apply hw
  have hAwder := congrArg (fun D => D U)
    ((mdifferentiableAt_const (c := (A : W →L[ℝ] W))).mvfderiv_clm_apply hw)
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hAwder
  change mvfderiv O (fun g : W ≃ₗᵢ[ℝ] W => (A : W →L[ℝ] W) (g.symm w)) 1 U =
    (A : W →L[ℝ] W) (mvfderiv O (fun g : W ≃ₗᵢ[ℝ] W => g.symm w) 1 U) at hAwder
  rw [LinearIsometryEquiv.mvfderiv_symm_apply_one] at hAwder
  have hc := congrArg (fun D => D U) (hbase.mvfderiv_clm_apply hAw)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    add_apply] at hc
  change mvfderiv O (fun g : W ≃ₗᵢ[ℝ] W => g ((A : W →L[ℝ] W) (g.symm w))) 1 U =
    mvfderiv O (fun g : W ≃ₗᵢ[ℝ] W => (A : W →L[ℝ] W) (g.symm w)) 1 U +
      mvfderiv O (fun g : W ≃ₗᵢ[ℝ] W => (g : W →L[ℝ] W)) 1 U ((A : W →L[ℝ] W) w) at hc
  rw [hAwder, ← LinearIsometryEquiv.coe_groupLieAlgebraEquiv U] at hc
  rw [hc, map_neg]
  exact neg_add_eq_sub _ _

theorem coe_mvfderiv_selfAdjointConjugation_one_apply
    (U : GroupLieAlgebra 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W)) (W ≃ₗᵢ[ℝ] W))
    (A : selfAdjoint.submodule ℝ (W →L[ℝ] W)) :
    (mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
      (fun g : W ≃ₗᵢ[ℝ] W => selfAdjointConjugation g) 1 U A : W →L[ℝ] W) =
      (LinearIsometryEquiv.groupLieAlgebraEquiv U : W →L[ℝ] W).comp (A : W →L[ℝ] W) -
        (A : W →L[ℝ] W).comp (LinearIsometryEquiv.groupLieAlgebraEquiv U : W →L[ℝ] W) := by
  let O := 𝓘(ℝ, skewAdjoint.submodule ℝ (W →L[ℝ] W))
  let ρ := selfAdjointConjugation (W := W)
  have hρ : MDifferentiableAt O
      𝓘(ℝ, (selfAdjoint.submodule ℝ (W →L[ℝ] W)) →L[ℝ]
        selfAdjoint.submodule ℝ (W →L[ℝ] W)) (fun g => ρ g) 1 :=
    (contMDiff_selfAdjointConjugation (n := 1) 1).mdifferentiableAt (by simp)
  have hρA := hρ.clm_apply (mdifferentiableAt_const (c := A))
  have hρAder := congrArg (fun L => L U)
    (hρ.mvfderiv_clm_apply (mdifferentiableAt_const (c := A)))
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hρAder
  apply ContinuousLinearMap.ext
  intro w
  let L : selfAdjoint.submodule ℝ (W →L[ℝ] W) →L[ℝ] W :=
    (ContinuousLinearMap.apply ℝ W w).comp (selfAdjoint.submodule ℝ (W →L[ℝ] W)).subtypeL
  have he := congrArg (fun D => D U)
    ((mdifferentiableAt_const (c := L)).mvfderiv_clm_apply hρA)
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply, hρAder] at he
  change mvfderiv O (fun g : W ≃ₗᵢ[ℝ] W => g ((A : W →L[ℝ] W) (g.symm w))) 1 U =
    (mvfderiv O (fun g => ρ g) 1 U A : W →L[ℝ] W) w at he
  change (mvfderiv O (fun g => ρ g) 1 U A : W →L[ℝ] W) w = _
  rw [← he]
  exact mvfderiv_conjugation_one_apply U (A : W →L[ℝ] W) w

end ContRepresentation
