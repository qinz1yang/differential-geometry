import DifferentialGeometry.Topology.Manifold.PartialAtlas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.CompleteLattice.Finset
open Set

namespace DifferentialGeometry.Topology.Manifold.AtlasOn

universe u v

theorem nonempty_univ_of_chart_union
    {H : Type u} {X : Type v} [TopologicalSpace H] [TopologicalSpace X] [CompactSpace X]
    [ChartedSpace H X] (G : StructureGroupoid H)
    (hunion : ∀ (s : Finset X) (x : X),
      AtlasOn G (⋃ y ∈ s, (chartAt H y).source) →
      Nonempty (AtlasOn G ((⋃ y ∈ s, (chartAt H y).source) ∪
        (chartAt H x).source))) :
    Nonempty (AtlasOn G (univ : Set X)) := by
  classical
  have key : ∀ s : Finset X,
      Nonempty (AtlasOn G (⋃ x ∈ s, (chartAt H x).source)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨(AtlasOn.empty G).congr (by simp)⟩
    | insert a s _ ih =>
      obtain ⟨A⟩ := ih
      obtain ⟨C⟩ := hunion s a A
      exact ⟨C.congr (by rw [Finset.set_biUnion_insert, union_comm])⟩
  obtain ⟨t, -, ht⟩ := (isCompact_univ (X := X)).elim_nhds_subcover
    (fun x : X => (chartAt H x).source)
    (fun x _ => chart_source_mem_nhds H x)
  obtain ⟨A⟩ := key t
  exact ⟨A.congr (univ_subset_iff.mp ht)⟩

end DifferentialGeometry.Topology.Manifold.AtlasOn
