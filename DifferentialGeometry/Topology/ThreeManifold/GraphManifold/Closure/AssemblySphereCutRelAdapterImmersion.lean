import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterDrill
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Embedding.FiniteDimension

/-!
# Chapter-14 assembly, relative COMPARE side adapters (e1): composing two drills

Lane ASM-L2f, group G1. The non-separating adapter drills the capped carrier twice; the doubly
drilled carrier embeds in the capped carrier through the composite of the two drill embeddings.
The composition of smooth embeddings between manifolds with boundary is not available in general;
here each drill embedding has a partial inverse off a closed tube, and every point of the doubly
drilled carrier is either sent off the first closed tube or (in the middle) off the second one.

* `isImmersionAtOfComplement_partialDiffeomorph_comp`,
  `isImmersionAtOfComplement_comp_partialDiffeomorph`: an immersion at a point composed with a
  partial diffeomorphism (same model) on either side.
* `isSmoothEmbedding_comp_of_partialInverses`: the composite of two drill embeddings is a smooth
  embedding (closed target: `IsSmoothEmbedding.comp_of_smoothBoundary`; target with boundary: the
  two pointwise lemmas).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Pointwise

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
  {W W' M N : Type*} [TopologicalSpace W] [ChartedSpace H W] [TopologicalSpace W']
  [ChartedSpace H W'] [TopologicalSpace M] [ChartedSpace G M] [TopologicalSpace N]
  [ChartedSpace G N]

/-- An immersion at a point followed by a partial diffeomorphism is an immersion there. -/
theorem isImmersionAtOfComplement_partialDiffeomorph_comp [IsManifold J ∞ N]
    (Φ : PartialDiffeomorph J J M N ∞) {f : W → M} {x : W}
    (hf : IsImmersionAtOfComplement F I J ∞ f x) (hfc : ContinuousAt f x) (hx : f x ∈ Φ.source) :
    IsImmersionAtOfComplement F I J ∞ (Φ ∘ f) x := by
  classical
  let U : Set W := interior (f ⁻¹' Φ.source)
  have hU : IsOpen U := isOpen_interior
  have hxU : x ∈ U :=
    mem_interior_iff_mem_nhds.mpr (hfc.preimage_mem_nhds (Φ.open_source.mem_nhds hx))
  let φ := hf.domChart.restr U
  let ψ := Φ.symm.toOpenPartialHomeomorph.trans hf.codChart
  have hψ : ψ ∈ IsManifold.maximalAtlas J ∞ N := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        (Φ.symm.contMDiffOn_toFun.mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
    · exact Φ.symm.contMDiffOn_invFun.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).mono
          (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
  have hφ : φ ∈ IsManifold.maximalAtlas I ∞ W :=
    restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hU
  have hfx : (Φ ∘ f) x ∈ ψ.source := by
    refine ⟨Φ.map_source hx, ?_⟩
    have hl : Φ.symm.toPartialEquiv (Φ.toPartialEquiv (f x)) = f x := Φ.toPartialEquiv.left_inv hx
    change Φ.symm.toPartialEquiv (Φ.toPartialEquiv (f x)) ∈ hf.codChart.source
    rw [hl]
    exact hf.mem_codChart_source
  have hcont : ContinuousAt (Φ ∘ f) x :=
    (Φ.contMDiffOn_toFun.continuousOn.continuousAt (Φ.open_source.mem_nhds hx)).comp hfc
  apply IsImmersionAtOfComplement.mk_of_continuousAt hcont hf.equiv φ ψ
    (by change x ∈ hf.domChart.source ∩ interior U
        rw [hU.interior_eq]
        exact ⟨hf.mem_domChart_source, hxU⟩) hfx hφ hψ
  intro z hz
  have hm : (hf.domChart.extend I).symm z ∈ hf.domChart.source ∩ U := by
    simpa only [OpenPartialHomeomorph.extend_source, φ,
      OpenPartialHomeomorph.restr_source, hU.interior_eq,
      OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
      OpenPartialHomeomorph.restr_symm_apply] using (φ.extend I).map_target hz
  have hz' : z ∈ (hf.domChart.extend I).target := by
    have hz₁ := hz
    simp only [φ, OpenPartialHomeomorph.extend_target,
      OpenPartialHomeomorph.restr_target, hU.interior_eq] at hz₁ ⊢
    exact ⟨hz₁.1.1, hz₁.2⟩
  have hleft : Φ.symm.toPartialEquiv (Φ.toPartialEquiv (f ((hf.domChart.extend I).symm z))) =
      f ((hf.domChart.extend I).symm z) :=
    Φ.toPartialEquiv.left_inv (interior_subset (s := f ⁻¹' Φ.source) hm.2)
  change J (hf.codChart (Φ.symm.toPartialEquiv
    (Φ.toPartialEquiv (f ((hf.domChart.extend I).symm z))))) = _
  rw [hleft]
  exact hf.writtenInCharts hz'

/-- A partial diffeomorphism followed by an immersion at the image point is an immersion. -/
theorem isImmersionAtOfComplement_comp_partialDiffeomorph [IsManifold I ∞ W']
    (Φ : PartialDiffeomorph I I W' W ∞) {f : W → M} {x : W'} (hx : x ∈ Φ.source)
    (hf : IsImmersionAtOfComplement F I J ∞ f (Φ x)) :
    IsImmersionAtOfComplement F I J ∞ (f ∘ Φ) x := by
  classical
  let ψ := Φ.toOpenPartialHomeomorph.trans hf.domChart
  have hψ : ψ ∈ IsManifold.maximalAtlas I ∞ W' := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hf.domChart_mem_maximalAtlas).comp
        (Φ.contMDiffOn_toFun.mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
    · exact Φ.contMDiffOn_invFun.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hf.domChart_mem_maximalAtlas).mono
          (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2)
  apply IsImmersionAtOfComplement.mk_of_charts hf.equiv ψ hf.codChart
    ⟨hx, hf.mem_domChart_source⟩ hf.mem_codChart_source hψ hf.codChart_mem_maximalAtlas
  · intro y hy
    exact hf.source_subset_preimage_source hy.2
  · intro z hz
    have hz₁ := hz
    simp only [ψ, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target,
      mem_inter_iff, mem_preimage] at hz₁
    have hz' : z ∈ (hf.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hz₁.1.1, hz₁.2⟩
    have hright : Φ.toPartialEquiv (Φ.symm.toPartialEquiv (hf.domChart.symm (I.symm z))) =
        hf.domChart.symm (I.symm z) :=
      Φ.toPartialEquiv.right_inv hz₁.1.2
    change J (hf.codChart (f (Φ.toPartialEquiv (Φ.symm.toPartialEquiv
      (hf.domChart.symm (I.symm z)))))) = _
    rw [hright]
    exact hf.writtenInCharts hz'

end Pointwise

/-- **The composite of two drill embeddings is a smooth embedding.** `η₁ : L₁ ↪ C` and
`η₂ : L₂ ↪ L₁` have partial inverses `O₁`, `O₂` (with `O.target = η ⁻¹' O.source`); every point of
`L₂` is sent by `η₁ ∘ η₂` into the source of `O₁` or by `η₂` into the source of `O₂`. -/
theorem isSmoothEmbedding_comp_of_partialInverses {C L₁ L₂ : CompactCarrier.{u}}
    (hk₁ : L₁.kind = .withBoundary) (hk₂ : L₂.kind = .withBoundary)
    {η₁ : L₁.Carrier → C.Carrier} {η₂ : L₂.Carrier → L₁.Carrier}
    (hη₁ : IsSmoothEmbedding L₁.model C.model ∞ η₁)
    (hη₂ : IsSmoothEmbedding L₂.model L₁.model ∞ η₂)
    (O₁ : PartialDiffeomorph C.model L₁.model C.Carrier L₁.Carrier ∞)
    (hO₁ : ∀ y, y ∈ O₁.source → η₁ (O₁ y) = y) (hO₁t : O₁.target = η₁ ⁻¹' O₁.source)
    (O₂ : PartialDiffeomorph L₁.model L₂.model L₁.Carrier L₂.Carrier ∞)
    (hO₂ : ∀ y, y ∈ O₂.source → η₂ (O₂ y) = y) (hO₂t : O₂.target = η₂ ⁻¹' O₂.source)
    (hcover : ∀ x, η₁ (η₂ x) ∈ O₁.source ∨ η₂ x ∈ O₂.source) :
    IsSmoothEmbedding L₂.model C.model ∞ (η₁ ∘ η₂) := by
  refine ⟨?_, hη₁.isEmbedding.comp hη₂.isEmbedding⟩
  obtain ⟨kC⟩ := C
  obtain ⟨k₁⟩ := L₁
  obtain ⟨k₂⟩ := L₂
  change k₁ = .withBoundary at hk₁
  change k₂ = .withBoundary at hk₂
  subst hk₁ hk₂
  cases kC with
  | closed => exact (IsSmoothEmbedding.comp_of_smoothBoundary hη₁ hη₂).isImmersion
  | withBoundary =>
    have h₁ := hη₁.isImmersion.isImmersionOfComplement_of_finrank_eq
      (C := EuclideanSpace ℝ (Fin 0)) (by simp)
    have h₂ := hη₂.isImmersion.isImmersionOfComplement_of_finrank_eq
      (C := EuclideanSpace ℝ (Fin 0)) (by simp)
    refine IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin 0)) fun x => ?_
    rcases hcover x with hx | hx
    · have hxt : η₂ x ∈ O₁.target := by
        rw [hO₁t]
        exact hx
      have hev : O₁.symm ∘ η₂ =ᶠ[𝓝 x] η₁ ∘ η₂ := by
        filter_upwards [hη₂.contMDiff.continuous.continuousAt.preimage_mem_nhds
          (O₁.open_target.mem_nhds hxt)] with z hz
        exact RelativeDrill.symm_apply_of_mem_target O₁ hO₁ hz
      exact (isImmersionAtOfComplement_partialDiffeomorph_comp O₁.symm (h₂ x)
        hη₂.contMDiff.continuous.continuousAt hxt).congr_of_eventuallyEq hev
    · have hxt : x ∈ O₂.target := by
        rw [hO₂t]
        exact hx
      have hsx : O₂.symm x = η₂ x := RelativeDrill.symm_apply_of_mem_target O₂ hO₂ hxt
      have hev : η₁ ∘ O₂.symm =ᶠ[𝓝 x] η₁ ∘ η₂ := by
        filter_upwards [O₂.open_target.mem_nhds hxt] with z hz
        change η₁ (O₂.symm z) = η₁ (η₂ z)
        rw [RelativeDrill.symm_apply_of_mem_target O₂ hO₂ hz]
      have h₁x := h₁ (η₂ x)
      rw [← hsx] at h₁x
      exact (isImmersionAtOfComplement_comp_partialDiffeomorph O₂.symm hxt
        h₁x).congr_of_eventuallyEq hev

end GC.GraphManifold.Assembly
