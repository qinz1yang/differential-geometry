import Mathlib.Topology.MetricSpace.GromovHausdorff

namespace GromovHausdorff

open Metric Set

theorem ghDist_subtype_le_of_net {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (s : Set X) [CompactSpace s] [Nonempty s]
    {ε : ℝ} (hε : 0 ≤ ε) (hnet : ∀ x : X, ∃ y : s, dist x y.val ≤ ε) :
    ghDist X s ≤ ε := by
  calc
    ghDist X s ≤ hausdorffDist (univ : Set X) s := by
      simpa using ghDist_le_hausdorffDist (isometry_id : Isometry (id : X → X))
        (isometry_subtype_coe : Isometry (Subtype.val : s → X))
    _ ≤ ε := by
      apply hausdorffDist_le_of_mem_dist hε
      · intro x _
        obtain ⟨y, hy⟩ := hnet x
        exact ⟨y.val, y.property, hy⟩
      · intro y _
        exact ⟨y, mem_univ y, by simpa using hε⟩

theorem ghDist_finset_le_of_net {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (S : Finset X) [Nonempty S]
    {ε : ℝ} (hε : 0 ≤ ε) (hnet : ∀ x : X, ∃ y ∈ S, dist x y ≤ ε) :
    ghDist X S ≤ ε := by
  apply ghDist_subtype_le_of_net (S : Set X) hε
  intro x
  obtain ⟨y, hy, hxy⟩ := hnet x
  exact ⟨⟨y, hy⟩, hxy⟩

end GromovHausdorff
