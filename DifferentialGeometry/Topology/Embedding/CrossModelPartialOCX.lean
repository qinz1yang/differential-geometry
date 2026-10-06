import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX

/-!
# Cross-model immersions, part 4: composition with a PARTIAL diffeomorphism (lane O-CROSS, G4)

Variants of the composition kernels of `CrossModelLinearOCX` / `CrossModelHalfSpaceOCX` where the
second map is only a partial diffeomorphism `Θ` whose source contains the image of the immersion
(e.g. the inclusion of the interior `W° → W` of a carrier, `interiorInclusion_BDRY1`):

* `IsImmersionAtOfComplement.partialDiffeomorph_comp_OCX` (one model `J`): the code chart is
  `Θ⁻¹` followed by the old code chart;
* `IsImmersionAtOfComplement.partialDiffeomorph_comp_toHalfSpace_OCX` (`𝓘(ℝ, ℝⁿ) → 𝓡∂ n`): the
  vector chart `Θ⁻¹ ≫ B` and the affine vector-chart kernel;
* global forms `IsImmersion.partialDiffeomorph_comp_OCX`,
  `IsImmersion.partialDiffeomorph_comp_toHalfSpace_OCX`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Same

variable {E' G : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace G]
  {J : ModelWithCorners ℝ E' G} {N₀ N : Type*} [TopologicalSpace N₀] [ChartedSpace G N₀]
  [TopologicalSpace N] [ChartedSpace G N]

/-- **An immersion followed by a partial diffeomorphism of one model** (source of `Θ` containing
the image) is an immersion. -/
theorem IsImmersionAtOfComplement.partialDiffeomorph_comp_OCX [IsManifold J ∞ N]
    {f : M → N₀} {x : M} (hf : IsImmersionAtOfComplement F I J ∞ f x)
    (Θ : PartialDiffeomorph J J N₀ N ∞) (hsrc : ∀ y, f y ∈ Θ.source) :
    IsImmersionAtOfComplement F I J ∞ (Θ ∘ f) x := by
  let ψ := Θ.symm.trans (chartPartialDiffeomorph_OCX hf.codChart hf.codChart_mem_maximalAtlas)
  have hleft : ∀ y, Θ.symm (Θ (f y)) = f y := fun y => Θ.left_inv (hsrc y)
  have hψ : ∀ y, f y ∈ hf.codChart.source → Θ (f y) ∈ ψ.source := by
    intro y hy
    refine ⟨Θ.map_source (hsrc y), ?_⟩
    change Θ.symm (Θ (f y)) ∈ hf.codChart.source
    rw [hleft]
    exact hy
  apply IsImmersionAtOfComplement.mk_of_charts hf.equiv hf.domChart ψ.toOpenPartialHomeomorph
    hf.mem_domChart_source (hψ x hf.mem_codChart_source) hf.domChart_mem_maximalAtlas
    ψ.mem_maximalAtlas_OCX (fun y hy => hψ y (hf.source_subset_preimage_source hy))
  intro u hu
  change J (hf.codChart (Θ.symm (Θ (f ((hf.domChart.extend I).symm u))))) = hf.equiv (u, 0)
  rw [hleft]
  exact hf.writtenInCharts hu

/-- Global form of `IsImmersionAtOfComplement.partialDiffeomorph_comp_OCX`. -/
theorem IsImmersion.partialDiffeomorph_comp_OCX [IsManifold J ∞ N] {f : M → N₀}
    (hf : IsImmersion I J ∞ f) (Θ : PartialDiffeomorph J J N₀ N ∞)
    (hsrc : ∀ y, f y ∈ Θ.source) : IsImmersion I J ∞ (Θ ∘ f) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hf
  let _ := hFg
  let _ := hFs
  exact IsImmersionOfComplement.isImmersion
    (fun x => (hF x).partialDiffeomorph_comp_OCX Θ hsrc)

end Same

section HalfSpace

variable {n : ℕ} [NeZero n]
  {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]

/-- **An immersion into an `𝓘(ℝ, ℝⁿ)`-manifold followed by a partial diffeomorphism onto an
`𝓡∂ n`-manifold** (source containing the image) is an immersion. -/
theorem IsImmersionAtOfComplement.partialDiffeomorph_comp_toHalfSpace_OCX [IsManifold I ∞ M]
    [IsManifold (𝓡∂ n) ∞ N] (s₀ : E) (hs₀ : s₀ ≠ 0)
    (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I) {f : M → N₀} {x : M}
    (hf : IsImmersionAtOfComplement F I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f x)
    (Θ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) N₀ N ∞)
    (hsrc : ∀ y, f y ∈ Θ.source) :
    IsImmersionAtOfComplement F I (𝓡∂ n) ∞ (Θ ∘ f) x := by
  let β := Θ.symm.trans (chartPartialDiffeomorph_OCX hf.codChart hf.codChart_mem_maximalAtlas)
  have hleft : ∀ y, Θ.symm (Θ (f y)) = f y := fun y => Θ.left_inv (hsrc y)
  refine isImmersionAtOfComplement_halfSpace_of_affine_OCX s₀ hs₀ hs₀I hf.domChart
    hf.domChart_mem_maximalAtlas hf.mem_domChart_source β ?_ hf.equiv 0 ?_
  · intro y hy
    refine ⟨Θ.map_source (hsrc y), ?_⟩
    change Θ.symm (Θ (f y)) ∈ hf.codChart.source
    rw [hleft]
    exact hf.source_subset_preimage_source hy
  · intro u hu
    change hf.codChart (Θ.symm (Θ (f ((hf.domChart.extend I).symm u)))) = hf.equiv (u, 0) + 0
    rw [hleft, add_zero]
    exact hf.writtenInCharts hu

/-- Global form of `IsImmersionAtOfComplement.partialDiffeomorph_comp_toHalfSpace_OCX`. -/
theorem IsImmersion.partialDiffeomorph_comp_toHalfSpace_OCX [IsManifold I ∞ M]
    [IsManifold (𝓡∂ n) ∞ N] (s₀ : E) (hs₀ : s₀ ≠ 0)
    (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I) {f : M → N₀}
    (hf : IsImmersion I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (Θ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) N₀ N ∞)
    (hsrc : ∀ y, f y ∈ Θ.source) : IsImmersion I (𝓡∂ n) ∞ (Θ ∘ f) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hf
  let _ := hFg
  let _ := hFs
  exact IsImmersionOfComplement.isImmersion
    (fun x => (hF x).partialDiffeomorph_comp_toHalfSpace_OCX s₀ hs₀ hs₀I Θ hsrc)

end HalfSpace

end Manifold
