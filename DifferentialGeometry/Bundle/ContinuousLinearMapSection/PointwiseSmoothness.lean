import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [FiniteDimensional 𝕜 F₂]
variable {n : WithTop ℕ∞}

lemma contMDiffAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
  have : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  have : FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let g : (Fin (Module.finrank 𝕜 F₁) → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, g (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffAt IB 𝓘(𝕜, Fin _ → F₂) n (evalBasis ∘ A) x :=
    contMDiffAt_pi_space.mpr fun i => h (bF₁ i)
  have hcompose : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hcompose]
  exact g.contDiff.contMDiff.contMDiffAt.comp _ hEA

lemma contMDiffWithinAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {s : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt IB 𝓘(𝕜, F₂) n (fun q => A q v) s x) :
    ContMDiffWithinAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A s x := by
  have : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  have : FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let g : (Fin (Module.finrank 𝕜 F₁) → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, g (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffWithinAt IB 𝓘(𝕜, Fin _ → F₂) n (evalBasis ∘ A) s x :=
    contMDiffWithinAt_pi_space.mpr fun i => h (bF₁ i)
  have hcompose : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hcompose]
  exact g.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt _ hEA
