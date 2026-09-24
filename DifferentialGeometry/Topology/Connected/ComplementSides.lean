import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocallyPathConnected

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Topology

theorem exists_mem_connectedComponentIn_inter_of_open_neighborhood
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {S O : Set X} (hS : IsClosed S) (hSne : S.Nonempty) (hO : IsOpen O) (hSO : S ⊆ O)
    (x : X) (hx : x ∈ Sᶜ) :
    ∃ y, y ∈ connectedComponentIn Sᶜ x ∧ y ∈ O := by
  by_contra h
  have havoid : connectedComponentIn Sᶜ x ⊆ Oᶜ := by
    intro y hy hyo
    exact h ⟨y, hy, hyo⟩
  have hclosure : closure (connectedComponentIn Sᶜ x) ⊆ Sᶜ := by
    intro y hy hys
    exact closure_minimal havoid hO.isClosed_compl hy (hSO hys)
  have hclosed : IsClosed (connectedComponentIn Sᶜ x) :=
    closure_subset_iff_isClosed.mp
      (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hx)) hclosure)
  have huniv : connectedComponentIn Sᶜ x = univ :=
    (IsClopen.eq_univ ⟨hclosed, hS.isOpen_compl.connectedComponentIn⟩
      ⟨x, mem_connectedComponentIn hx⟩)
  obtain ⟨s, hs⟩ := hSne
  have hsmem : s ∈ connectedComponentIn Sᶜ x := by rw [huniv]; exact mem_univ s
  exact connectedComponentIn_subset Sᶜ x hsmem hs

theorem complement_eq_union_components_of_two_local_sides
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {S O L U : Set X} (hS : IsClosed S) (hSne : S.Nonempty) (hO : IsOpen O)
    (hSO : S ⊆ O) (hlocal : O \ S = L ∪ U)
    (hL : IsPreconnected L) (hU : IsPreconnected U)
    {a b : X} (ha : a ∈ L) (hb : b ∈ U) :
    connectedComponentIn Sᶜ a ∪ connectedComponentIn Sᶜ b = Sᶜ ∧
      (connectedComponentIn Sᶜ a = connectedComponentIn Sᶜ b ∨
        Disjoint (connectedComponentIn Sᶜ a) (connectedComponentIn Sᶜ b)) ∧
      L ⊆ connectedComponentIn Sᶜ a ∧ U ⊆ connectedComponentIn Sᶜ b := by
  have hLsub : L ⊆ Sᶜ := by
    intro x hx
    exact (hlocal.symm ▸ Or.inl hx : x ∈ O \ S).2
  have hUsub : U ⊆ Sᶜ := by
    intro x hx
    exact (hlocal.symm ▸ Or.inr hx : x ∈ O \ S).2
  have hLA := hL.subset_connectedComponentIn ha hLsub
  have hUB := hU.subset_connectedComponentIn hb hUsub
  refine ⟨?_, ?_, hLA, hUB⟩
  · apply Subset.antisymm
      (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
    intro x hx
    obtain ⟨y, hyC, hyO⟩ :=
      exists_mem_connectedComponentIn_inter_of_open_neighborhood hS hSne hO hSO x hx
    have hyS := connectedComponentIn_subset Sᶜ x hyC
    rcases (hlocal ▸ (show y ∈ O \ S from ⟨hyO, hyS⟩)) with hyL | hyU
    · have heq := (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq (hLA hyL)).symm
      exact Or.inl (heq ▸ mem_connectedComponentIn hx)
    · have heq := (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq (hUB hyU)).symm
      exact Or.inr (heq ▸ mem_connectedComponentIn hx)
  · by_cases heq : connectedComponentIn Sᶜ a = connectedComponentIn Sᶜ b
    · exact Or.inl heq
    · right
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact heq ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm)

theorem joinedIn_or_disjoint_components_of_two_local_sides
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    {S O L U : Set X} (hS : IsClosed S) (hSne : S.Nonempty) (hO : IsOpen O)
    (hSO : S ⊆ O) (hlocal : O \ S = L ∪ U)
    (hL : IsPreconnected L) (hU : IsPreconnected U)
    {a b : X} (ha : a ∈ L) (hb : b ∈ U) :
    (IsConnected Sᶜ ∧ JoinedIn Sᶜ a b) ∨
      (Disjoint (connectedComponentIn Sᶜ a) (connectedComponentIn Sᶜ b) ∧
        connectedComponentIn Sᶜ a ∪ connectedComponentIn Sᶜ b = Sᶜ) := by
  obtain ⟨hunion, heq | hdisj, hLA, hUB⟩ :=
    complement_eq_union_components_of_two_local_sides hS hSne hO hSO hlocal hL hU ha hb
  · left
    rw [heq, union_self] at hunion
    have hbS : b ∈ Sᶜ := connectedComponentIn_subset Sᶜ b (hUB hb)
    have hconn : IsConnected Sᶜ := hunion ▸ isConnected_connectedComponentIn_iff.mpr hbS
    refine ⟨hconn, ?_⟩
    exact (hS.isOpen_compl.isConnected_iff_isPathConnected.mp hconn).joinedIn a
      (connectedComponentIn_subset Sᶜ a (hLA ha)) b hbS
  · exact Or.inr ⟨hdisj, hunion⟩

end DifferentialGeometry.Topology
