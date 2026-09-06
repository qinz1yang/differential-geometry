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

theorem ContMDiffWithinAt.clm_bundle_map
    {φ : ∀ x : M, V₁ x →L[𝕜] V₂ x} {s : Set M} {p : TotalSpace F₁ V₁}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => (⟨x, φ x⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p.1) :
    ContMDiffWithinAt (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun q : TotalSpace F₁ V₁ => (⟨q.1, φ q.1 q.2⟩ : TotalSpace F₂ V₂))
      (Bundle.TotalSpace.proj ⁻¹' s) p := by
  have h := hφ.comp p (contMDiff_proj (IB := I) (F := F₁) V₁ p).contMDiffWithinAt
    (Set.mapsTo_preimage _ _)
  exact h.clm_bundle_apply contMDiffWithinAt_id

theorem ContMDiffAt.clm_bundle_map
    {φ : ∀ x : M, V₁ x →L[𝕜] V₂ x} {p : TotalSpace F₁ V₁}
    (hφ : ContMDiffAt I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => (⟨x, φ x⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p.1) :
    ContMDiffAt (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun q : TotalSpace F₁ V₁ => (⟨q.1, φ q.1 q.2⟩ : TotalSpace F₂ V₂)) p := by
  have h := hφ.comp p (contMDiff_proj (F := F₁) V₁).contMDiffAt
  exact h.clm_bundle_apply contMDiffAt_id

theorem ContMDiffOn.clm_bundle_map
    {φ : ∀ x : M, V₁ x →L[𝕜] V₂ x} {s : Set M}
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => (⟨x, φ x⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    ContMDiffOn (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂))
      (Bundle.TotalSpace.proj ⁻¹' s) :=
  fun _ hp => (hφ _ hp).clm_bundle_map

theorem ContMDiff.clm_bundle_map
    {φ : ∀ x : M, V₁ x →L[𝕜] V₂ x}
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => (⟨x, φ x⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ V₂)) :=
  fun _ => (hφ _).clm_bundle_map

theorem MDifferentiableWithinAt.clm_bundle_comp
    (hψ : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))) s p₀)
    (hφ : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) s p₀ := by
  rw [mdifferentiableWithinAt_hom_bundle] at hψ hφ ⊢
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

theorem MDifferentiableAt.clm_bundle_comp
    (hψ : MDifferentiableAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))) p₀)
    (hφ : MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) p₀ :=
  MDifferentiableWithinAt.clm_bundle_comp hψ hφ

theorem MDifferentiableOn.clm_bundle_comp
    (hψ : MDifferentiableOn J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))) s)
    (hφ : MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) s :=
  fun p hp => (hψ p hp).clm_bundle_comp (hφ p hp)

theorem MDifferentiable.clm_bundle_comp
    (hψ : MDifferentiable J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, ψ p⟩ : TotalSpace (F₂ →L[𝕜] F₃)
        (fun x => V₂ x →L[𝕜] V₃ x))))
    (hφ : MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (ψ p).comp (φ p)⟩ : TotalSpace (F₁ →L[𝕜] F₃)
        (fun x => V₁ x →L[𝕜] V₃ x))) :=
  fun p => (hψ p).clm_bundle_comp (hφ p)


variable {U₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ U₁)]
  [∀ x, SeminormedAddCommGroup (U₁ x)] [∀ x, NormedSpace 𝕜 (U₁ x)]
  [FiberBundle F₁ U₁] [VectorBundle 𝕜 F₁ U₁]
  {U₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ U₂)]
  [∀ x, SeminormedAddCommGroup (U₂ x)] [∀ x, NormedSpace 𝕜 (U₂ x)]
  [FiberBundle F₂ U₂] [VectorBundle 𝕜 F₂ U₂]
  {U₃ : M → Type*} [TopologicalSpace (TotalSpace F₃ U₃)]
  [∀ x, SeminormedAddCommGroup (U₃ x)] [∀ x, NormedSpace 𝕜 (U₃ x)]
  [FiberBundle F₃ U₃] [VectorBundle 𝕜 F₃ U₃]

theorem ContinuousLinearMap.inCoordinates_flip {x₀ x : M}
    (φ : U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x)
    (h₁ : x ∈ (trivializationAt F₁ U₁ x₀).baseSet)
    (h₂ : x ∈ (trivializationAt F₂ U₂ x₀).baseSet)
    (h₃ : x ∈ (trivializationAt F₃ U₃ x₀).baseSet) :
    (inCoordinates F₁ U₁ (F₂ →L[𝕜] F₃) (fun y => U₂ y →L[𝕜] U₃ y)
      x₀ x x₀ x φ).flip =
      inCoordinates F₂ U₂ (F₁ →L[𝕜] F₃) (fun y => U₁ y →L[𝕜] U₃ y)
        x₀ x x₀ x φ.flip := by
  ext v w
  rw [flip_apply, inCoordinates_apply_eq₂ h₁ h₂ h₃,
    inCoordinates_apply_eq₂ h₂ h₁ h₃]
  rfl

theorem ContMDiffWithinAt.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) s p₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hφ ⊢
  refine ⟨hφ.1, ?_⟩
  let L : (F₁ →L[𝕜] F₂ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₁ →L[𝕜] F₃) :=
    (ContinuousLinearMap.flipₗᵢ 𝕜 F₁ F₂ F₃).toContinuousLinearEquiv.toContinuousLinearMap
  have hL := ContinuousLinearMap.contDiff (𝕜 := 𝕜)
    (E := F₁ →L[𝕜] F₂ →L[𝕜] F₃) (F := F₂ →L[𝕜] F₁ →L[𝕜] F₃) (n := n) L
  have h := hL.contDiffAt.contMDiffAt.comp_contMDiffWithinAt p₀ hφ.2
  let U := (trivializationAt F₁ U₁ (b p₀)).baseSet ∩
    (trivializationAt F₂ U₂ (b p₀)).baseSet ∩
    (trivializationAt F₃ U₃ (b p₀)).baseSet
  have hU : IsOpen U := ((trivializationAt F₁ U₁ (b p₀)).open_baseSet.inter
    (trivializationAt F₂ U₂ (b p₀)).open_baseSet).inter
    (trivializationAt F₃ U₃ (b p₀)).open_baseSet
  have hx : b p₀ ∈ U := ⟨⟨mem_baseSet_trivializationAt F₁ U₁ (b p₀),
    mem_baseSet_trivializationAt F₂ U₂ (b p₀)⟩, mem_baseSet_trivializationAt F₃ U₃ (b p₀)⟩
  apply h.congr_of_eventuallyEq
  · filter_upwards [hφ.1.continuousWithinAt (hU.mem_nhds hx)] with p hp
    exact (ContinuousLinearMap.inCoordinates_flip (φ p) hp.1.1 hp.1.2 hp.2).symm
  · exact (ContinuousLinearMap.inCoordinates_flip (φ p₀) hx.1.1 hx.1.2 hx.2).symm

theorem ContMDiffAt.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) p₀ :=
  ContMDiffWithinAt.clm_bundle_flip hφ

theorem ContMDiffOn.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) s :=
  fun p hp => (hφ p hp).clm_bundle_flip

theorem ContMDiff.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) :=
  fun p => (hφ p).clm_bundle_flip

theorem MDifferentiableWithinAt.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) s p₀ := by
  rw [mdifferentiableWithinAt_hom_bundle] at hφ ⊢
  refine ⟨hφ.1, ?_⟩
  let L : (F₁ →L[𝕜] F₂ →L[𝕜] F₃) →L[𝕜] (F₂ →L[𝕜] F₁ →L[𝕜] F₃) :=
    (ContinuousLinearMap.flipₗᵢ 𝕜 F₁ F₂ F₃).toContinuousLinearEquiv.toContinuousLinearMap
  have hL := ContinuousLinearMap.contDiff (𝕜 := 𝕜)
    (E := F₁ →L[𝕜] F₂ →L[𝕜] F₃) (F := F₂ →L[𝕜] F₁ →L[𝕜] F₃) (n := 1) L
  have h := (hL.contDiffAt.contMDiffAt.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt p₀ hφ.2
  let U := (trivializationAt F₁ U₁ (b p₀)).baseSet ∩
    (trivializationAt F₂ U₂ (b p₀)).baseSet ∩
    (trivializationAt F₃ U₃ (b p₀)).baseSet
  have hU : IsOpen U := ((trivializationAt F₁ U₁ (b p₀)).open_baseSet.inter
    (trivializationAt F₂ U₂ (b p₀)).open_baseSet).inter
    (trivializationAt F₃ U₃ (b p₀)).open_baseSet
  have hx : b p₀ ∈ U := ⟨⟨mem_baseSet_trivializationAt F₁ U₁ (b p₀),
    mem_baseSet_trivializationAt F₂ U₂ (b p₀)⟩, mem_baseSet_trivializationAt F₃ U₃ (b p₀)⟩
  apply h.congr_of_eventuallyEq
  · filter_upwards [hφ.1.continuousWithinAt (hU.mem_nhds hx)] with p hp
    exact (ContinuousLinearMap.inCoordinates_flip (φ p) hp.1.1 hp.1.2 hp.2).symm
  · exact (ContinuousLinearMap.inCoordinates_flip (φ p₀) hx.1.1 hx.1.2 hx.2).symm

theorem MDifferentiableAt.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) p₀ :=
  MDifferentiableWithinAt.clm_bundle_flip hφ

theorem MDifferentiableOn.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) s :=
  fun p hp => (hφ p hp).clm_bundle_flip

theorem MDifferentiable.clm_bundle_flip
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    (hφ : MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x)))) :
    MDifferentiable J (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).flip⟩ : TotalSpace (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (fun x => U₂ x →L[𝕜] U₁ x →L[𝕜] U₃ x))) :=
  fun p => (hφ p).clm_bundle_flip

variable {F₄ F₅ : Type*} [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  [NormedAddCommGroup F₅] [NormedSpace 𝕜 F₅]
  {U₄ : M → Type*} [TopologicalSpace (TotalSpace F₄ U₄)]
  [∀ x, SeminormedAddCommGroup (U₄ x)] [∀ x, NormedSpace 𝕜 (U₄ x)]
  [FiberBundle F₄ U₄] [VectorBundle 𝕜 F₄ U₄]
  {U₅ : M → Type*} [TopologicalSpace (TotalSpace F₅ U₅)]
  [∀ x, SeminormedAddCommGroup (U₅ x)] [∀ x, NormedSpace 𝕜 (U₅ x)]
  [FiberBundle F₅ U₅] [VectorBundle 𝕜 F₅ U₅]

theorem ContMDiffWithinAt.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s p₀)
    (hA : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))) s p₀)
    (hC : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂)) n
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) s p₀ := by
  have h₁ := hφ.clm_bundle_comp (F₁ := F₄) (F₂ := F₁) (F₃ := F₂ →L[𝕜] F₃)
    (V₁ := U₄) (V₂ := U₁) (V₃ := fun x => U₂ x →L[𝕜] U₃ x) hA
  have h₂ := h₁.clm_bundle_flip (F₁ := F₄) (F₂ := F₂) (F₃ := F₃)
    (U₁ := U₄) (U₂ := U₂) (U₃ := U₃)
  have h₃ := h₂.clm_bundle_comp (F₁ := F₅) (F₂ := F₂) (F₃ := F₄ →L[𝕜] F₃)
    (V₁ := U₅) (V₂ := U₂) (V₃ := fun x => U₄ x →L[𝕜] U₃ x) hC
  exact h₃.clm_bundle_flip (F₁ := F₅) (F₂ := F₄) (F₃ := F₃)
    (U₁ := U₅) (U₂ := U₄) (U₃ := U₃)

theorem ContMDiffAt.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) p₀)
    (hA : ContMDiffAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))) p₀)
    (hC : ContMDiffAt J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂)) n
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) p₀ :=
  ContMDiffWithinAt.clm_bundle_bilinearComp hφ hA hC

theorem ContMDiffOn.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s)
    (hA : ContMDiffOn J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))) s)
    (hC : ContMDiffOn J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂)) n
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) s :=
  fun p hp => (hφ p hp).clm_bundle_bilinearComp (hA p hp) (hC p hp)

theorem ContMDiff.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))))
    (hA : ContMDiff J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))))
    (hC : ContMDiff J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂)) n
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃)) n
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) :=
  fun p => (hφ p).clm_bundle_bilinearComp (hA p) (hC p)

theorem MDifferentiableWithinAt.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s p₀)
    (hA : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))) s p₀)
    (hC : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂))
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x))) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) s p₀ := by
  have h₁ := hφ.clm_bundle_comp (F₁ := F₄) (F₂ := F₁) (F₃ := F₂ →L[𝕜] F₃)
    (V₁ := U₄) (V₂ := U₁) (V₃ := fun x => U₂ x →L[𝕜] U₃ x) hA
  have h₂ := h₁.clm_bundle_flip (F₁ := F₄) (F₂ := F₂) (F₃ := F₃)
    (U₁ := U₄) (U₂ := U₂) (U₃ := U₃)
  have h₃ := h₂.clm_bundle_comp (F₁ := F₅) (F₂ := F₂) (F₃ := F₄ →L[𝕜] F₃)
    (V₁ := U₅) (V₂ := U₂) (V₃ := fun x => U₄ x →L[𝕜] U₃ x) hC
  exact h₃.clm_bundle_flip (F₁ := F₅) (F₂ := F₄) (F₃ := F₃)
    (U₁ := U₅) (U₂ := U₄) (U₃ := U₃)

theorem MDifferentiableAt.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) p₀)
    (hA : MDifferentiableAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))) p₀)
    (hC : MDifferentiableAt J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂))
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x))) p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) p₀ :=
  MDifferentiableWithinAt.clm_bundle_bilinearComp hφ hA hC

theorem MDifferentiableOn.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))) s)
    (hA : MDifferentiableOn J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))) s)
    (hC : MDifferentiableOn J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂))
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x))) s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) s :=
  fun p hp => (hφ p hp).clm_bundle_bilinearComp (hA p hp) (hC p hp)

theorem MDifferentiable.clm_bundle_bilinearComp
    {φ : ∀ p, U₁ (b p) →L[𝕜] U₂ (b p) →L[𝕜] U₃ (b p)}
    {A : ∀ p, U₄ (b p) →L[𝕜] U₁ (b p)}
    {C : ∀ p, U₅ (b p) →L[𝕜] U₂ (b p)}
    (hφ : MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun p => (⟨b p, φ p⟩ : TotalSpace (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (fun x => U₁ x →L[𝕜] U₂ x →L[𝕜] U₃ x))))
    (hA : MDifferentiable J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₁))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₄ →L[𝕜] F₁)
        (fun x => U₄ x →L[𝕜] U₁ x))))
    (hC : MDifferentiable J (I.prod 𝓘(𝕜, F₅ →L[𝕜] F₂))
      (fun p => (⟨b p, C p⟩ : TotalSpace (F₅ →L[𝕜] F₂)
        (fun x => U₅ x →L[𝕜] U₂ x)))) :
    MDifferentiable J (I.prod 𝓘(𝕜, F₄ →L[𝕜] F₅ →L[𝕜] F₃))
      (fun p => (⟨b p, (φ p).bilinearComp (A p) (C p)⟩ :
        TotalSpace (F₄ →L[𝕜] F₅ →L[𝕜] F₃)
          (fun x => U₄ x →L[𝕜] U₅ x →L[𝕜] U₃ x))) :=
  fun p => (hφ p).clm_bundle_bilinearComp (hA p) (hC p)

theorem ContMDiffWithinAt.clm_bundle_id (hb : ContMDiffWithinAt J I n b s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) n
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) s p₀ := by
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨hb, ?_⟩
  let e := trivializationAt F₁ U₁ (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F₁ U₁ (b p₀)
  have heq (p : P) (hp : b p ∈ e.baseSet) :
      ContinuousLinearMap.inCoordinates F₁ U₁ F₁ U₁ (b p₀) (b p) (b p₀) (b p)
        (ContinuousLinearMap.id 𝕜 (U₁ (b p))) = ContinuousLinearMap.id 𝕜 F₁ := by
    ext v
    exact e.continuousLinearMapAt_symmL hp v
  apply (contMDiffWithinAt_const (c := ContinuousLinearMap.id 𝕜 F₁)).congr_of_eventuallyEq
  · filter_upwards [hb.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact heq p hp
  · exact heq p₀ hx

theorem ContMDiffAt.clm_bundle_id (hb : ContMDiffAt J I n b p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) n
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) p₀ :=
  ContMDiffWithinAt.clm_bundle_id hb

theorem ContMDiffOn.clm_bundle_id (hb : ContMDiffOn J I n b s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) n
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) s :=
  fun p hp => (hb p hp).clm_bundle_id

theorem ContMDiff.clm_bundle_id (hb : ContMDiff J I n b) :
    ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) n
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) :=
  fun p => (hb p).clm_bundle_id

theorem MDifferentiableWithinAt.clm_bundle_id (hb : MDifferentiableWithinAt J I b s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁))
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) s p₀ := by
  rw [mdifferentiableWithinAt_hom_bundle]
  refine ⟨hb, ?_⟩
  let e := trivializationAt F₁ U₁ (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F₁ U₁ (b p₀)
  have heq (p : P) (hp : b p ∈ e.baseSet) :
      ContinuousLinearMap.inCoordinates F₁ U₁ F₁ U₁ (b p₀) (b p) (b p₀) (b p)
        (ContinuousLinearMap.id 𝕜 (U₁ (b p))) = ContinuousLinearMap.id 𝕜 F₁ := by
    ext v
    exact e.continuousLinearMapAt_symmL hp v
  apply (mdifferentiableWithinAt_const (c := ContinuousLinearMap.id 𝕜 F₁)).congr_of_eventuallyEq
  · filter_upwards [hb.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact heq p hp
  · exact heq p₀ hx

theorem MDifferentiableAt.clm_bundle_id (hb : MDifferentiableAt J I b p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁))
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) p₀ :=
  MDifferentiableWithinAt.clm_bundle_id hb

theorem MDifferentiableOn.clm_bundle_id (hb : MDifferentiableOn J I b s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁))
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) s :=
  fun p hp => (hb p hp).clm_bundle_id

theorem MDifferentiable.clm_bundle_id (hb : MDifferentiable J I b) :
    MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₁))
      (fun p => (⟨b p, ContinuousLinearMap.id 𝕜 (U₁ (b p))⟩ :
        TotalSpace (F₁ →L[𝕜] F₁) (fun x => U₁ x →L[𝕜] U₁ x))) :=
  fun p => (hb p).clm_bundle_id

theorem ContMDiffWithinAt.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁)) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂)) n
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) s p₀ := by
  have hb := ((contMDiffWithinAt_totalSpace (F := F₁)).mp hσ).1
  have hi := hb.clm_bundle_id (F₁ := F₁ →L[𝕜] F₂) (U₁ := fun x => U₁ x →L[𝕜] U₂ x)
  have hf := hi.clm_bundle_flip (F₁ := F₁ →L[𝕜] F₂) (F₂ := F₁) (F₃ := F₂)
    (U₁ := fun x => U₁ x →L[𝕜] U₂ x) (U₂ := U₁) (U₃ := U₂)
  exact hf.clm_bundle_apply (F₁ := F₁) (F₂ := (F₁ →L[𝕜] F₂) →L[𝕜] F₂)
    (E₁ := U₁) (E₂ := fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x) hσ

theorem ContMDiffAt.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : ContMDiffAt J (I.prod 𝓘(𝕜, F₁)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁)) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂)) n
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) p₀ :=
  ContMDiffWithinAt.clm_bundle_eval hσ

theorem ContMDiffOn.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : ContMDiffOn J (I.prod 𝓘(𝕜, F₁)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁)) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂)) n
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) s :=
  fun p hp => (hσ p hp).clm_bundle_eval

theorem ContMDiff.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : ContMDiff J (I.prod 𝓘(𝕜, F₁)) n
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁))) :
    ContMDiff J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂)) n
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) :=
  fun p => (hσ p).clm_bundle_eval

theorem MDifferentiableWithinAt.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁)) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂))
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) s p₀ := by
  have hb := ((mdifferentiableWithinAt_totalSpace (F := F₁) I _).mp hσ).1
  have hi := hb.clm_bundle_id (F₁ := F₁ →L[𝕜] F₂) (U₁ := fun x => U₁ x →L[𝕜] U₂ x)
  have hf := hi.clm_bundle_flip (F₁ := F₁ →L[𝕜] F₂) (F₂ := F₁) (F₃ := F₂)
    (U₁ := fun x => U₁ x →L[𝕜] U₂ x) (U₂ := U₁) (U₃ := U₂)
  exact hf.clm_bundle_apply (F₁ := F₁) (F₂ := (F₁ →L[𝕜] F₂) →L[𝕜] F₂)
    (E₁ := U₁) (E₂ := fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x) hσ

theorem MDifferentiableAt.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : MDifferentiableAt J (I.prod 𝓘(𝕜, F₁))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁)) p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂))
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) p₀ :=
  MDifferentiableWithinAt.clm_bundle_eval hσ

theorem MDifferentiableOn.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : MDifferentiableOn J (I.prod 𝓘(𝕜, F₁))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁)) s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂))
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) s :=
  fun p hp => (hσ p hp).clm_bundle_eval

theorem MDifferentiable.clm_bundle_eval
    {σ : ∀ p, U₁ (b p)}
    (hσ : MDifferentiable J (I.prod 𝓘(𝕜, F₁))
      (fun p => (⟨b p, σ p⟩ : TotalSpace F₁ U₁))) :
    MDifferentiable J (I.prod 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₂))
      (fun p => (⟨b p, ContinuousLinearMap.apply 𝕜 (U₂ (b p)) (σ p)⟩ :
        TotalSpace ((F₁ →L[𝕜] F₂) →L[𝕜] F₂)
          (fun x => (U₁ x →L[𝕜] U₂ x) →L[𝕜] U₂ x))) :=
  fun p => (hσ p).clm_bundle_eval
