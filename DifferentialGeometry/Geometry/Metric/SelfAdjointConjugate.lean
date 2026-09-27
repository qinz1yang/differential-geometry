import DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle
import DifferentialGeometry.Bundle.Equiv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
variable {n : ℕ∞ω}
  [ContMDiffVectorBundle n F₁ V₁ I] [IsContMDiffRiemannianBundle I n F₁ V₁]
  [ContMDiffVectorBundle n F₂ V₂ I] [IsContMDiffRiemannianBundle I n F₂ V₂]

namespace ContMDiffSection

def selfAdjointConjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap)) :
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := n)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := n)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    Cₛ^n⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯ →
      Cₛ^n⟮I; Fin S₁.rank → ℝ, fun x => S₁.fiber x⟯ := by
  letI : CompleteSpace F₁ := FiniteDimensional.complete ℝ F₁
  letI : ∀ x, FiniteDimensional ℝ (V₁ x) := fun x =>
    VectorBundle.finiteDimensional ℝ F₁ V₁ x
  letI : ∀ x, FiniteDimensional ℝ (V₂ x) := fun x =>
    VectorBundle.finiteDimensional ℝ F₂ V₂ x
  letI : ∀ x, CompleteSpace (V₁ x) := fun x => FiniteDimensional.complete ℝ (V₁ x)
  letI : ∀ x, CompleteSpace (V₂ x) := fun x => FiniteDimensional.complete ℝ (V₂ x)
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := n)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := n)
  letI := S₁.totalSpaceTopology
  letI := S₁.fiberBundle
  letI := S₂.totalSpaceTopology
  letI := S₂.fiberBundle
  dsimp only
  intro A
  let a : ∀ x, S₁.fiber x := fun x =>
    ⟨(φ x).symm.conjStarAlgEquiv (A x),
      IsSelfAdjoint.map (A x).property (φ x).symm.conjStarAlgEquiv⟩
  refine ⟨a, (S₁.contMDiff_section_iff a).mpr ?_⟩
  have hA := (S₂.contMDiff_section_iff A).mp A.contMDiff
  have hφinv : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) n
      (fun x => TotalSpace.mk' (F₂ →L[ℝ] F₁) x
        (φ x).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa only [ContinuousLinearMap.inverse_equiv,
      LinearIsometryEquiv.toContinuousLinearEquiv_symm] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  exact hφinv.clm_bundle_comp (hA.clm_bundle_comp hφ)

theorem selfAdjointConjugate_coe
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap)) :
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := n)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := n)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    ∀ (A : Cₛ^n⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯) (x : M),
      (selfAdjointConjugate φ hφ A x : V₁ x →L[ℝ] V₁ x) =
        (φ x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((A x : V₂ x →L[ℝ] V₂ x).comp
            (φ x).toContinuousLinearEquiv.toContinuousLinearMap) := by
  intros
  rfl

end ContMDiffSection
