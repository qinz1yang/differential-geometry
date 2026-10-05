import Mathlib.Topology.Compactness.Compact

open scoped Topology
open Set

namespace IsCompact

variable {T M : Type*} [TopologicalSpace T] [TopologicalSpace M]

theorem exists_compact_superset_of_eventually {K : Set T} (hK : IsCompact K)
    (B : T → Set M)
    (hB : ∀ t ∈ K, ∃ L : Set M, IsCompact L ∧
      ∀ᶠ s in 𝓝[K] t, B s ⊆ L) :
    ∃ L : Set M, IsCompact L ∧ ∀ t ∈ K, B t ⊆ L := by
  classical
  choose L hL hnear using hB
  obtain ⟨S, hS⟩ := hK.elim_nhdsWithin_subcover'
    (fun t ht => {s | B s ⊆ L t ht}) hnear
  refine ⟨⋃ t ∈ S, L t t.property, S.isCompact_biUnion (fun t _ => hL t t.property), ?_⟩
  intro t ht x hx
  rcases mem_iUnion₂.mp (hS ht) with ⟨s, hs, hst⟩
  exact mem_iUnion₂.mpr ⟨s, hs, hst hx⟩

end IsCompact
