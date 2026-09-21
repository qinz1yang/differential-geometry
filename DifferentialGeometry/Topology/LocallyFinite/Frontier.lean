import Mathlib.Topology.LocallyFinite

open Set

namespace LocallyFinite

theorem frontier_iUnion_subset {X ι : Type*} [TopologicalSpace X]
    {s : ι → Set X} (hs : LocallyFinite s) :
    frontier (⋃ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  have hc := hx.1
  rw [hs.closure_iUnion] at hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  exact mem_iUnion.mpr ⟨i, hi, fun h => hx.2 (interior_mono (subset_iUnion s i) h)⟩

end LocallyFinite
