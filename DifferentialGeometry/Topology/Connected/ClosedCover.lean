import Mathlib.Topology.Connected.Basic

open Set

namespace DifferentialGeometry.Topology

theorem connectedComponentIn_sdiff_inter_eq_sdiff
    {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (hA : IsClosed A) (hB : IsClosed B) (hconn : IsPreconnected (A \ B)) (hx : x ∈ A \ B) :
    connectedComponentIn ((A ∪ B) \ (A ∩ B)) x = A \ B := by
  have hsub : A \ B ⊆ (A ∪ B) \ (A ∩ B) := fun _ hy =>
    ⟨Or.inl hy.1, fun hz => hy.2 hz.2⟩
  have hxC := mem_connectedComponentIn (hsub hx)
  apply Subset.antisymm _ (hconn.subset_connectedComponentIn hx hsub)
  intro y hy
  have hyU := connectedComponentIn_subset ((A ∪ B) \ (A ∩ B)) x hy
  have hyA : y ∈ A := by
    by_contra hynot
    obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn
      A B hA hB ((connectedComponentIn_subset _ _).trans sdiff_subset)
      ⟨x, hxC, hx.1⟩ ⟨y, hy, hyU.1.resolve_left hynot⟩
    exact (connectedComponentIn_subset _ _ hz).2 ⟨hzA, hzB⟩
  exact ⟨hyA, fun hyB => hyU.2 ⟨hyA, hyB⟩⟩

end DifferentialGeometry.Topology
