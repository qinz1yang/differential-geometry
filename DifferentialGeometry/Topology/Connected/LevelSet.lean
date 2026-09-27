import Mathlib.Topology.Order.IntermediateValue

open Set

namespace DifferentialGeometry.Topology

variable {X α : Type*} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α] {S : Set X} {f : X → α} {r : α} {p : X}

theorem connectedComponentIn_sdiff_fiber_eq_inter_lt
    (hf : ContinuousOn f S) (hconn : IsPreconnected (S ∩ {x | f x < r}))
    (hp : p ∈ S ∩ {x | f x < r}) :
    connectedComponentIn (S \ {x | f x = r}) p = S ∩ {x | f x < r} := by
  have hsub : S ∩ {x | f x < r} ⊆ S \ {x | f x = r} :=
    fun _ hx => ⟨hx.1, (show f _ < r from hx.2).ne⟩
  apply Subset.antisymm _ (hconn.subset_connectedComponentIn hp hsub)
  intro x hx
  have hxS := connectedComponentIn_subset (S \ {x | f x = r}) p hx
  refine ⟨hxS.1, ?_⟩
  change f x < r
  by_contra h
  have hpx := mem_connectedComponentIn (hsub hp)
  obtain ⟨y, hy, hyr⟩ := isPreconnected_connectedComponentIn.intermediate_value hpx hx
    (hf.mono ((connectedComponentIn_subset _ _).trans sdiff_subset))
    ⟨(show f p < r from hp.2).le, le_of_not_gt h⟩
  exact (connectedComponentIn_subset _ _ hy).2 hyr

theorem connectedComponentIn_sdiff_fiber_eq_inter_gt
    (hf : ContinuousOn f S) (hconn : IsPreconnected (S ∩ {x | r < f x}))
    (hp : p ∈ S ∩ {x | r < f x}) :
    connectedComponentIn (S \ {x | f x = r}) p = S ∩ {x | r < f x} := by
  exact connectedComponentIn_sdiff_fiber_eq_inter_lt (α := αᵒᵈ) hf hconn hp

end DifferentialGeometry.Topology
