import DifferentialGeometry.Geometry.Connection.Subbundle
import DifferentialGeometry.Bundle.Hom

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

omit [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle ∞ F₁ V₁ I]
    [ContMDiffVectorBundle ∞ F₂ V₂ I] in
theorem isCovariantlyInvariantSubmoduleFamily_map
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (φ x).toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (C : CovariantDerivative I F₂ V₂)
    (hcomm : ∀ (u : Cₛ^∞⟮I; F₁, V₁⟯) (x : M) (X : TangentSpace I x),
      C (fun y => φ y (u y)) x X = φ x (D u x X))
    (S : ∀ x, Submodule ℝ (V₁ x))
    (hS : IsCovariantlyInvariantSubmoduleFamily D S) :
    IsCovariantlyInvariantSubmoduleFamily C (fun x => (S x).map (φ x).toLinearMap) := by
  have hφinv := hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  simp only [ContinuousLinearMap.inverse_equiv] at hφinv
  intro v U hU hv x hx X
  let u : Cₛ^∞⟮I; F₁, V₁⟯ :=
    ⟨fun y => (φ y).symm (v y), hφinv.clm_bundle_apply v.contMDiff⟩
  have hu : ∀ y ∈ U, u y ∈ S y := by
    intro y hy
    obtain ⟨w, hw, heq⟩ := hv y hy
    change (φ y).symm (v y) ∈ S y
    change φ y w = v y at heq
    rw [← heq, ContinuousLinearEquiv.symm_apply_apply]
    exact hw
  have hDu := hS u U hU hu x hx X
  refine ⟨D u x X, hDu, ?_⟩
  have hmap : (fun y => φ y (u y)) = v := by
    funext y
    exact (φ y).apply_symm_apply (v y)
  exact (hcomm u x X).symm.trans (congrArg (fun v => C v x X) hmap)

omit [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle ∞ F₁ V₁ I]
    [ContMDiffVectorBundle ∞ F₂ V₂ I] in
theorem isCovariantlyInvariantSubmoduleFamily_map_iff
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (φ x).toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (C : CovariantDerivative I F₂ V₂)
    (hcomm : ∀ (u : Cₛ^∞⟮I; F₁, V₁⟯) (x : M) (X : TangentSpace I x),
      C (fun y => φ y (u y)) x X = φ x (D u x X))
    (S : ∀ x, Submodule ℝ (V₁ x))
    : IsCovariantlyInvariantSubmoduleFamily C (fun x => (S x).map (φ x).toLinearMap) ↔
      IsCovariantlyInvariantSubmoduleFamily D S := by
  constructor
  · intro hS u U hU hu x hx X
    let v : Cₛ^∞⟮I; F₂, V₂⟯ := ⟨fun y => φ y (u y), hφ.clm_bundle_apply u.contMDiff⟩
    have hv : ∀ y ∈ U, v y ∈ (S y).map (φ y).toLinearMap := by
      intro y hy
      exact ⟨u y, hu y hy, rfl⟩
    obtain ⟨w, hw, heq⟩ := hS v U hU hv x hx X
    change φ x w = C (fun y => φ y (u y)) x X at heq
    rw [hcomm] at heq
    exact (φ x).injective heq ▸ hw
  · exact isCovariantlyInvariantSubmoduleFamily_map φ hφ D C hcomm S

end DifferentialGeometry.Geometry.Connection
