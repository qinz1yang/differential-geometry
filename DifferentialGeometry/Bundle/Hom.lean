import Mathlib.Geometry.Manifold.VectorBundle.Hom

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {n : WithTop ℕ∞}
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul 𝕜 (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {V₃ : M → Type*} [TopologicalSpace (TotalSpace F₃ V₃)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [∀ x, IsTopologicalAddGroup (V₃ x)]
  [∀ x, ContinuousSMul 𝕜 (V₃ x)] [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]
  {b : P → M} {φ : ∀ p : P, V₁ (b p) →L[𝕜] V₂ (b p)}
  {ψ : ∀ p : P, V₂ (b p) →L[𝕜] V₃ (b p)} {s : Set P} {p₀ : P}

theorem ContMDiffWithinAt.clm_bundle_comp
    (hψ : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))) s p₀)
    (hφ : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) s p₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hψ hφ ⊢
  refine ⟨hφ.1, ?_⟩
  have h := hψ.2.clm_comp hφ.2
  let e := trivializationAt F₂ V₂ (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F₂ V₂ (b p₀)
  have heq : ∀ p, b p ∈ e.baseSet →
      ContinuousLinearMap.inCoordinates F₁ V₁ F₃ V₃
          (b p₀) (b p) (b p₀) (b p) ((ψ p).comp (φ p)) =
        (ContinuousLinearMap.inCoordinates F₂ V₂ F₃ V₃
          (b p₀) (b p) (b p₀) (b p) (ψ p)).comp
          (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂
            (b p₀) (b p) (b p₀) (b p) (φ p)) := by
    intro p hp
    ext v
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt _ hp]
  apply h.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p in 𝓝[s] p₀, b p ∈ e.baseSet :=
      hφ.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)
    filter_upwards [hbase] with p hp
    exact heq p hp
  · exact heq p₀ hx

theorem ContMDiffAt.clm_bundle_comp
    (hψ : ContMDiffAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))) p₀)
    (hφ : ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) p₀ :=
  ContMDiffWithinAt.clm_bundle_comp hψ hφ

theorem ContMDiffOn.clm_bundle_comp
    (hψ : ContMDiffOn J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))) s)
    (hφ : ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) s :=
  fun p hp => (hψ p hp).clm_bundle_comp (hφ p hp)

theorem ContMDiff.clm_bundle_comp
    (hψ : ContMDiff J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))))
    (hφ : ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) :=
  fun p => (hψ p).clm_bundle_comp (hφ p)
