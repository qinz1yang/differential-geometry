import DifferentialGeometry.Geometry.Connection.Pullback

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul 𝕜 (V₁ x)] [FiberBundle F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [FiniteDimensional 𝕜 F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [∀ x, T2Space (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

theorem pullbackFiberwiseLinearEquiv_apply_eq_of_const_smul
    (φ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (cov : CovariantDerivative I F₂ V₂) (a : 𝕜)
    (ψ : ∀ x, V₁ x ≃ₗ[𝕜] V₂ x)
    (hψ : ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) 1
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, ψ p.1 p.2⟩ : TotalSpace F₂ V₂)))
    (hψa : ∀ y v, ψ y v = a • φ y v)
    {σ : ∀ x, V₁ x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁)) (T% σ) x)
    (X : TangentSpace I x) :
    pullbackFiberwiseLinearEquiv ψ hψ cov σ x X =
      pullbackFiberwiseLinearEquiv φ hφ cov σ x X := by
  rw [pullbackFiberwiseLinearEquiv_apply ψ hψ cov σ x X,
    pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X]
  have hmap : MDifferentiableAt I (I.prod 𝓘(𝕜, F₂))
      (T% (fun y => φ y (σ y))) x :=
    (hφ.mdifferentiableAt (by norm_num)).comp x hσ
  have hc := congrArg (fun L => L X) (cov.isCovariantDerivativeOnUniv.smul_const a hmap)
  have hsec : (fun y => ψ y (σ y)) = (fun y => a • φ y (σ y)) := by
    funext y
    exact hψa y (σ y)
  rw [hsec]
  apply (ψ x).injective
  rw [LinearEquiv.apply_symm_apply, hψa, LinearEquiv.apply_symm_apply]
  exact hc

end CovariantDerivative
