import DifferentialGeometry.Topology.Attachment.Union
import DifferentialGeometry.Topology.Handle.Basic

namespace DifferentialGeometry.Topology.Handle

universe u v

open Set

private theorem range_attachingInclusion_of_disjoint {k l : ℕ} {Y : Type v} {X₀ : Set Y}
    (c : StandardHandle k l → Y)
    (hmeet : Disjoint (c '' (Set.univ \ attachingRegion k l)) X₀) :
    ∀ d : StandardHandle k l, c d ∈ X₀ → d ∈ Set.range (attachingInclusion k l) := by
  intro d hd
  by_contra hnot
  have hd' : d ∈ Set.univ \ attachingRegion k l := by
    constructor
    · trivial
    · intro hmem
      exact hnot (by simpa [range_attachingInclusion k l] using hmem)
  exact (Set.disjoint_left.mp hmeet) ⟨d, hd', rfl⟩ hd

theorem adjunction_coherence {k l : ℕ} {X : Type u} (φ : AttachingRegion k l → X)
    (a : AttachingRegion k l) :
    cell φ (attachingInclusion k l a) = lower φ (φ a) :=
  DifferentialGeometry.Topology.adjunction_coherence (attachingInclusion k l) φ a

theorem continuous_lower {k l : ℕ} {X : Type u} [TopologicalSpace X] (φ : AttachingRegion k l → X) :
    Continuous (lower φ) :=
  continuous_adjunctionLower (i := attachingInclusion k l) φ

theorem continuous_cell {k l : ℕ} {X : Type u} [TopologicalSpace X] (φ : AttachingRegion k l → X) :
    Continuous (cell φ) :=
  continuous_adjunctionCell (attachingInclusion k l) φ

theorem cell_lower_cover {k l : ℕ} {X : Type u} (φ : AttachingRegion k l → X)
    (z : AdjunctionSpace k l φ) :
    z ∈ Set.range (cell φ) ∪ Set.range (lower φ) := by
  refine Quot.induction_on z ?_
  intro s
  rcases s with d | x
  · exact Or.inl ⟨d, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

theorem cell_lower_coverage {k l : ℕ} {X : Type u} (φ : AttachingRegion k l → X) :
    (Set.range (cell φ) ∪ Set.range (lower φ)) = Set.univ := by
  ext z
  constructor <;> intro hz
  · trivial
  · exact cell_lower_cover φ z

section UnionRealization

variable {k l : ℕ} {Y : Type v} [TopologicalSpace Y] {X₀ : Set Y}
variable (φ : AttachingRegion k l → X₀) (c : StandardHandle k l → Y)
variable (hφ : ∀ a : AttachingRegion k l, (φ a : Y) = c (attachingInclusion k l a))
variable (hc : Function.Injective c) (hcont : Continuous c)
variable (hmeet : Disjoint (c '' (Set.univ \ attachingRegion k l)) X₀)
variable (hclosed : IsClosed X₀)
variable [T2Space Y]

noncomputable def adjunctionHomeomorphUnionImage :
    AdjunctionSpace k l φ ≃ₜ {y : Y // y ∈ X₀ ∪ Set.range c} :=
  DifferentialGeometry.Topology.adjunctionHomeomorphUnionImage
    (i := attachingInclusion k l) φ c hφ hc hcont
    (range_attachingInclusion_of_disjoint c hmeet) hclosed

theorem adjunctionHomeomorphUnionImage_lower (x : X₀) :
    adjunctionHomeomorphUnionImage φ c hφ hc hcont hmeet hclosed (lower φ x) =
      ⟨x, Or.inl x.2⟩ := by
  change DifferentialGeometry.Topology.adjunctionHomeomorphUnionImage
    (i := attachingInclusion k l) φ c hφ hc hcont
    (range_attachingInclusion_of_disjoint c hmeet) hclosed
    (DifferentialGeometry.Topology.adjunctionLower (i := attachingInclusion k l) φ x) =
    ⟨x, Or.inl x.2⟩
  exact DifferentialGeometry.Topology.adjunctionHomeomorphUnionImage_lower
    (i := attachingInclusion k l) φ c hφ hc hcont
    (range_attachingInclusion_of_disjoint c hmeet) hclosed x

theorem adjunctionHomeomorphUnionImage_cell (d : StandardHandle k l) :
    adjunctionHomeomorphUnionImage φ c hφ hc hcont hmeet hclosed (cell φ d) =
      ⟨c d, Or.inr ⟨d, rfl⟩⟩ := by
  change DifferentialGeometry.Topology.adjunctionRealization X₀ (attachingInclusion k l) c φ hφ
    (DifferentialGeometry.Topology.adjunctionCell (attachingInclusion k l) φ d) =
    ⟨c d, Or.inr ⟨d, rfl⟩⟩
  dsimp [DifferentialGeometry.Topology.adjunctionRealization,
    DifferentialGeometry.Topology.adjunctionUnionMap,
    DifferentialGeometry.Topology.adjunctionCell, DifferentialGeometry.Topology.adjunctionMk]

theorem adjunctionHomeomorphUnionImage_attachingRegion (a : AttachingRegion k l) :
    adjunctionHomeomorphUnionImage φ c hφ hc hcont hmeet hclosed
        (cell φ (attachingInclusion k l a)) =
      adjunctionHomeomorphUnionImage φ c hφ hc hcont hmeet hclosed (lower φ (φ a)) := by
  rw [adjunction_coherence φ a]

end UnionRealization

end DifferentialGeometry.Topology.Handle
