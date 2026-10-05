import DifferentialGeometry.Geometry.Connection.HomBundle.Basic

noncomputable section

open Bundle DifferentialGeometry
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  {V₃ : M → Type*} [TopologicalSpace (TotalSpace F₃ V₃)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [∀ x, IsTopologicalAddGroup (V₃ x)]
  [∀ x, ContinuousSMul ℝ (V₃ x)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]

theorem hom_comp
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    (cov₃ : CovariantDerivative I F₃ V₃)
    {φ : ∀ x, V₁ x →L[ℝ] V₂ x} {ψ : ∀ x, V₂ x →L[ℝ] V₃ x} {x : M}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun y => (⟨y, φ y⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))) x)
    (hψ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₃))
      (fun y => (⟨y, ψ y⟩ : TotalSpace (F₂ →L[ℝ] F₃)
        (fun y => V₂ y →L[ℝ] V₃ y))) x)
    (v : TangentSpace I x) :
    hom I M F₁ V₁ F₃ V₃ cov₁ cov₃
        (fun y => (ψ y).comp (φ y)) x v =
      (hom I M F₂ V₂ F₃ V₃ cov₂ cov₃ ψ x v).comp (φ x) +
        (ψ x).comp (hom I M F₁ V₁ F₂ V₂ cov₁ cov₂ φ x v) := by
  ext w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁)
    (V := V₁) (n := (⊤ : ℕ∞)) x w
  rw [← hX, ← hY]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [hom_apply_of_mdifferentiableAt I M F₁ V₁ F₃ V₃
    cov₁ cov₃ _ (hψ.clm_bundle_comp hφ) X.mdifferentiableAt Y.mdifferentiableAt]
  rw [hom_apply_of_mdifferentiableAt I M F₂ V₂ F₃ V₃
    cov₂ cov₃ _ hψ X.mdifferentiableAt (hφ.clm_bundle_apply Y.mdifferentiableAt)]
  rw [hom_apply_of_mdifferentiableAt I M F₁ V₁ F₂ V₂
    cov₁ cov₂ _ hφ X.mdifferentiableAt Y.mdifferentiableAt]
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

end CovariantDerivative
