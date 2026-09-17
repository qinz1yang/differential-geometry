import DifferentialGeometry.Topology.SphereSeparation.ReconstructionRegions
import DifferentialGeometry.Topology.SphereSeparation.NormalChartHalves

open Set Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

variable {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
  {e : SphereTwo → N}

theorem exists_neighborhood_connected_endSide_subset_of_normalChart
    {x : SphereTwo} (c₀ : EmbeddedSphereNormalChart e x) (d : SphereSides (range e))
    {O : Set N} (hO : IsOpen O) (hx : e x ∈ O) :
    ∃ U : Set N, IsOpen U ∧ e x ∈ U ∧ U ⊆ O ∧ IsConnected (d.endSide ∩ U) := by
  obtain ⟨c, hpos, hneg, hcO⟩ := c₀.exists_connectedHalves_subset hO hx
  have hnot := not_both_normalHalves_subset_of_twoSidedCover d.disjoint d.union_eq_compl
    d.closure_compactSide d.closure_endSide c
  refine ⟨c.neighborhood, c.isOpen_neighborhood, c.image_mem_neighborhood, hcO, ?_⟩
  rcases d.subset_compactSide_or_subset_endSide hpos.isPreconnected
    c.positiveHalf_subset_compl_range with hp | hp <;>
    rcases d.subset_compactSide_or_subset_endSide hneg.isPreconnected
      c.negativeHalf_subset_compl_range with hn | hn
  · exact False.elim (hnot.1 ⟨hp, hn⟩)
  · have heq : d.endSide ∩ c.neighborhood = c.negativeHalf := by
      apply Subset.antisymm
      · intro y hy
        have hh : y ∈ c.positiveHalf ∪ c.negativeHalf := by
          rw [← c.neighborhood_diff_range_eq_halves]
          exact ⟨hy.2, d.endSide_subset_compl hy.1⟩
        exact hh.resolve_left (fun h => d.disjoint.le_bot ⟨hp h, hy.1⟩)
      · intro y hy
        exact ⟨hn hy, hy.1⟩
    exact heq.symm ▸ hneg
  · have heq : d.endSide ∩ c.neighborhood = c.positiveHalf := by
      apply Subset.antisymm
      · intro y hy
        have hh : y ∈ c.positiveHalf ∪ c.negativeHalf := by
          rw [← c.neighborhood_diff_range_eq_halves]
          exact ⟨hy.2, d.endSide_subset_compl hy.1⟩
        exact hh.resolve_right (fun h => d.disjoint.le_bot ⟨hn h, hy.1⟩)
      · intro y hy
        exact ⟨hp hy, hy.1⟩
    exact heq.symm ▸ hpos
  · exact False.elim (hnot.2 ⟨hp, hn⟩)

theorem exists_neighborhood_connected_endSide_subset
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) (d : SphereSides (range e))
    (x : SphereTwo) {O : Set N} (hO : IsOpen O) (hx : e x ∈ O) :
    ∃ U : Set N, IsOpen U ∧ e x ∈ U ∧ U ⊆ O ∧ IsConnected (d.endSide ∩ U) :=
  exists_neighborhood_connected_endSide_subset_of_normalChart
    (Classical.choice (embeddedSphereNormalChart_nonempty he x)) d hO hx

namespace SphereSides

variable {S S₂ : Set N}

private theorem exists_shared_boundary_neighborhood
    (d₁ : SphereSides (range e))
    (hlocal : ∀ z, e z ∉ S → Nonempty (EmbeddedSphereNormalChart e z))
    {x : N} (hx : x ∈ range e ∪ S₂) (hxS : x ∉ S) {O : Set N} (hO : IsOpen O) (hxO : x ∈ O)
    (heq : range e ∩ O = S₂ ∩ O) :
    ∃ U : Set N, IsOpen U ∧ x ∈ range e ∩ U ∧
      range e ∩ U = S₂ ∩ U ∧ IsPreconnected (d₁.endSide ∩ U) := by
  have hx₁ : x ∈ range e := by
    rcases hx with hx | hx
    · exact hx
    · exact (heq.symm.subset ⟨hx, hxO⟩).1
  obtain ⟨z, rfl⟩ := hx₁
  obtain ⟨U, hU, hxU, hUO, hconn⟩ :=
    exists_neighborhood_connected_endSide_subset_of_normalChart
      (Classical.choice (hlocal z hxS)) d₁ hO hxO
  refine ⟨U, hU, ⟨mem_range_self z, hxU⟩, ?_, hconn.isPreconnected⟩
  ext y
  constructor
  · intro hy
    exact ⟨(heq.subset ⟨hy.1, hUO hy.2⟩).1, hy.2⟩
  · intro hy
    exact ⟨(heq.symm.subset ⟨hy.1, hUO hy.2⟩).1, hy.2⟩

theorem nested_reconstruction_regions_of_local_normal_charts
    (hlocal : ∀ z, e z ∉ S → Nonempty (EmbeddedSphereNormalChart e z))
    (d : SphereSides S) (d₁ : SphereSides (range e)) (d₂ : SphereSides S₂)
    (hproper : d₁.compactSide ⊂ d₂.compactSide) (hS : S ⊆ range e ∪ S₂)
    (hpatch : ∀ x ∈ (range e ∪ S₂) \ S, ∃ O : Set N, IsOpen O ∧ x ∈ O ∧
      range e ∩ O = S₂ ∩ O) :
    d.compactSide = d₂.compactSide \ closure d₁.compactSide ∧
      closure d₂.compactSide = closure d.compactSide ∪ closure d₁.compactSide ∧
      closure d.compactSide ∩ closure d₁.compactSide = S ∩ range e := by
  apply d.nested_reconstruction_regions d₁ d₂ hproper hS
  intro x hx
  obtain ⟨O, hO, hxO, heq⟩ := hpatch x hx
  obtain ⟨U, hU, hxU, hUeq, hconn⟩ :=
    exists_shared_boundary_neighborhood d₁ hlocal hx.1 hx.2 hO hxO heq
  exact ⟨U, hU, hxU.2,
    d₁.compactSide_inter_eq_of_subset_of_boundary_inter_eq d₂ hproper.subset hU hxU hUeq hconn⟩

theorem nested_reconstruction_regions_of_local_boundary_eq
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (d : SphereSides S) (d₁ : SphereSides (range e)) (d₂ : SphereSides S₂)
    (hproper : d₁.compactSide ⊂ d₂.compactSide) (hS : S ⊆ range e ∪ S₂)
    (hpatch : ∀ x ∈ (range e ∪ S₂) \ S, ∃ O : Set N, IsOpen O ∧ x ∈ O ∧
      range e ∩ O = S₂ ∩ O) :
    d.compactSide = d₂.compactSide \ closure d₁.compactSide ∧
      closure d₂.compactSide = closure d.compactSide ∪ closure d₁.compactSide ∧
      closure d.compactSide ∩ closure d₁.compactSide = S ∩ range e :=
  nested_reconstruction_regions_of_local_normal_charts
    (fun z _ => embeddedSphereNormalChart_nonempty he z) d d₁ d₂ hproper hS hpatch

theorem disjoint_reconstruction_regions_of_local_normal_charts
    (hlocal : ∀ z, e z ∉ S → Nonempty (EmbeddedSphereNormalChart e z))
    (d : SphereSides S) (d₁ : SphereSides (range e)) (d₂ : SphereSides S₂)
    (hd : Disjoint d₁.compactSide d₂.compactSide)
    (hS : S = closure (((range e) \ S₂) ∪ (S₂ \ range e)))
    (hpatch : ∀ x ∈ (range e ∪ S₂) \ S, ∃ O : Set N, IsOpen O ∧ x ∈ O ∧
      range e ∩ O = S₂ ∩ O) :
    closure d.compactSide = closure d₁.compactSide ∪ closure d₂.compactSide ∧
      closure d₁.compactSide ∩ closure d₂.compactSide = range e ∩ S₂ := by
  apply d.disjoint_reconstruction_regions d₁ d₂ hd hS
  intro x hx
  obtain ⟨O, hO, hxO, heq⟩ := hpatch x hx
  obtain ⟨U, hU, hxU, hUeq, hconn⟩ :=
    exists_shared_boundary_neighborhood d₁ hlocal hx.1 hx.2 hO hxO heq
  exact d₁.subset_union_closures_of_disjoint_of_boundary_inter_eq d₂ hd hU hxU hUeq hconn hxU.2

theorem disjoint_reconstruction_regions_of_local_boundary_eq
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (d : SphereSides S) (d₁ : SphereSides (range e)) (d₂ : SphereSides S₂)
    (hd : Disjoint d₁.compactSide d₂.compactSide)
    (hS : S = closure (((range e) \ S₂) ∪ (S₂ \ range e)))
    (hpatch : ∀ x ∈ (range e ∪ S₂) \ S, ∃ O : Set N, IsOpen O ∧ x ∈ O ∧
      range e ∩ O = S₂ ∩ O) :
    closure d.compactSide = closure d₁.compactSide ∪ closure d₂.compactSide ∧
      closure d₁.compactSide ∩ closure d₂.compactSide = range e ∩ S₂ :=
  disjoint_reconstruction_regions_of_local_normal_charts
    (fun z _ => embeddedSphereNormalChart_nonempty he z) d d₁ d₂ hd hS hpatch

end SphereSides
end DifferentialGeometry.Topology.SphereSeparation
