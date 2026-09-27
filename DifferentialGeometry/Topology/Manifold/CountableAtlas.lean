import Mathlib.Geometry.Manifold.ChartedSpace

namespace DifferentialGeometry.Topology.Manifold


theorem secondCountableTopology_of_compact {E M : Type*} [TopologicalSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [SecondCountableTopology E] [CompactSpace M] :
    SecondCountableTopology M := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt E x).source) (fun x => (chartAt E x).open_source)
    (show (Set.univ : Set M) ⊆ ⋃ x, (chartAt E x).source from
      fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  exact ChartedSpace.secondCountable_of_countable_cover E
    (Set.eq_univ_of_subset hs rfl) s.countable_toSet

end DifferentialGeometry.Topology.Manifold
