import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω}
  {b : P → M} {σ : ∀ p, V (b p)} {s : Set P} {p₀ : P}

section ContMDiff

variable [IsContMDiffRiemannianBundle I n F V]

theorem ContMDiffWithinAt.innerSL_bundle
    (hσ : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V)) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s p₀ := by
  obtain ⟨g, hg, heq⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle I n F V).exists_contMDiff
  have hb := ((contMDiffWithinAt_totalSpace (F := F)).mp hσ).1
  have hgc : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, g (b p)⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] V x →L[ℝ] ℝ))) s p₀ :=
    (hg (b p₀)).comp_contMDiffWithinAt p₀ hb
  have h := hgc.clm_bundle_apply (F₂ := F →L[ℝ] ℝ)
    (E₂ := fun x => V x →L[ℝ] ℝ) hσ
  convert h using 1
  funext p
  congr 1
  ext w
  exact heq (b p) (σ p) w

theorem ContMDiffAt.innerSL_bundle
    (hσ : ContMDiffAt J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V)) p₀) :
    ContMDiffAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) p₀ :=
  ContMDiffWithinAt.innerSL_bundle hσ

theorem ContMDiffOn.innerSL_bundle
    (hσ : ContMDiffOn J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V)) s) :
    ContMDiffOn J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s :=
  fun p hp => (hσ p hp).innerSL_bundle

theorem ContMDiff.innerSL_bundle
    (hσ : ContMDiff J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V))) :
    ContMDiff J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) :=
  fun p => (hσ p).innerSL_bundle

end ContMDiff

section MDifferentiable

variable [IsContMDiffRiemannianBundle I 1 F V]

theorem MDifferentiableWithinAt.innerSL_bundle
    (hσ : MDifferentiableWithinAt J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V)) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s p₀ := by
  obtain ⟨g, hg, heq⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle I 1 F V).exists_contMDiff
  have hb := ((mdifferentiableWithinAt_totalSpace (F := F) I _).mp hσ).1
  have hgc : MDifferentiableWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ))
      (fun p => (⟨b p, g (b p)⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] V x →L[ℝ] ℝ))) s p₀ :=
    ((hg (b p₀)).mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt p₀ hb
  have h := hgc.clm_bundle_apply (F₂ := F →L[ℝ] ℝ)
    (E₂ := fun x => V x →L[ℝ] ℝ) hσ
  convert h using 1
  funext p
  congr 1
  ext w
  exact heq (b p) (σ p) w

theorem MDifferentiableAt.innerSL_bundle
    (hσ : MDifferentiableAt J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V)) p₀) :
    MDifferentiableAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) p₀ :=
  MDifferentiableWithinAt.innerSL_bundle hσ

theorem MDifferentiableOn.innerSL_bundle
    (hσ : MDifferentiableOn J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V)) s) :
    MDifferentiableOn J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s :=
  fun p hp => (hσ p hp).innerSL_bundle

theorem MDifferentiable.innerSL_bundle
    (hσ : MDifferentiable J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F V))) :
    MDifferentiable J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) :=
  fun p => (hσ p).innerSL_bundle

end MDifferentiable
