import DifferentialGeometry.Topology.Homology.ChainSupport



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}



def integralSingularSmallChains (n : ℕ) (U : ι → Set X) :
    Submodule ℤ ((integralSingularChains X).X n) :=
  ⨆ i, integralSingularChainsIn n (U i)



theorem integralSingularSmallChains_eq_span_basis (n : ℕ) (U : ι → Set X) :
    integralSingularSmallChains n U = Submodule.span ℤ
      (integralSingularChainBasis n X ''
        {σ | ∃ i, range (integralSingularSimplexEquiv n X σ) ⊆ U i}) := by
  unfold integralSingularSmallChains
  simp_rw [integralSingularChainsIn_eq_span_basis]
  rw [← Submodule.span_iUnion, ← Set.image_iUnion]
  have hs : (⋃ i, {σ | range (integralSingularSimplexEquiv n X σ) ⊆ U i}) =
      {σ | ∃ i, range (integralSingularSimplexEquiv n X σ) ⊆ U i} := by
    ext σ
    simp
  rw [hs]



theorem integralSingularSmallChains_mem_iff (n : ℕ) (U : ι → Set X)
    (c : (integralSingularChains X).X n) :
    c ∈ integralSingularSmallChains n U ↔
      ∀ σ : integralSingularSimplex n X, integralSingularChainRepr n X c σ ≠ 0 →
        ∃ i, range (integralSingularSimplexEquiv n X σ) ⊆ U i := by
  rw [integralSingularSmallChains_eq_span_basis, (integralSingularChainBasis n X).mem_span_image]
  change (↑(integralSingularChainRepr n X c).support : Set _) ⊆
    {σ | ∃ i, range (integralSingularSimplexEquiv n X σ) ⊆ U i} ↔ _
  constructor
  · intro h σ hσ
    exact h (Finsupp.mem_support_iff.mpr hσ)
  · intro h σ hσ
    exact h σ (Finsupp.mem_support_iff.mp hσ)


theorem integralSingularSmallChains_boundary (n : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X (n + 1)} (hc : c ∈ integralSingularSmallChains (n + 1) U) :
    (integralSingularChains X).d (n + 1) n c ∈ integralSingularSmallChains n U := by
  have h : integralSingularSmallChains (n + 1) U ≤
      Submodule.comap ((integralSingularChains X).d (n + 1) n).hom
        (integralSingularSmallChains n U) := by
    apply iSup_le
    intro i b hb
    exact Submodule.mem_iSup_of_mem i (integralSingularChainsIn_boundary n (U i) hb)
  exact h hc



theorem integralSingularSmallChains_d (i j : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X i} (hc : c ∈ integralSingularSmallChains i U) :
    (integralSingularChains X).d i j c ∈ integralSingularSmallChains j U := by
  by_cases h : j + 1 = i
  · subst i
    exact integralSingularSmallChains_boundary j U hc
  · rw [(integralSingularChains X).shape i j h]
    exact Submodule.zero_mem _


theorem integralSingularSmallChains_refinement {κ : Type*} (n : ℕ)
    (U : ι → Set X) (V : κ → Set X) (h : ∀ i, ∃ j, U i ⊆ V j) :
    integralSingularSmallChains n U ≤ integralSingularSmallChains n V := by
  intro c hc
  rw [integralSingularSmallChains_mem_iff] at hc ⊢
  intro σ hσ
  obtain ⟨i, hi⟩ := hc σ hσ
  obtain ⟨j, hj⟩ := h i
  exact ⟨j, hi.trans hj⟩

end DifferentialGeometry.Topology
