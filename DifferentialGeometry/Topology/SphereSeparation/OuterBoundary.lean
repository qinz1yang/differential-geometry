import DifferentialGeometry.Topology.SphereSeparation.CollarSide
import DifferentialGeometry.Topology.SphereSeparation.BallSideRelations
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Topology

namespace Poincare.Topology.SphereSeparation

theorem interior_subset_compactSide_or_of_two_boundary_collars
    {B C X : Type*} [TopologicalSpace B] [ConnectedSpace B]
    [TopologicalSpace C] [ConnectedSpace C]
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    {e : B → X} {f : C → X}
    (c : ThreeManifold.TwoSidedCollar e) (d : ThreeManifold.TwoSidedCollar f)
    (s : SphereSides (range e)) (t : SphereSides (range f))
    {K : Set X} (hK : IsCompact K) (hconn : IsPreconnected (interior K))
    (hfront : frontier K = range e ∪ range f)
    (hc : ∀ p, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hd : ∀ p, d.toFun p ∈ K ↔ p.2 ≤ 0) :
    interior K ⊆ s.compactSide ∨ interior K ⊆ t.compactSide := by
  have havoid : interior K ⊆ (range e ∪ range f)ᶜ := by
    rw [← hfront]
    intro x hx hf
    exact (disjoint_interior_frontier (s := K)).le_bot ⟨hx, hf⟩
  rcases s.subset_compactSide_or_subset_endSide hconn
      (fun _ hx he ↦ havoid hx (Or.inl he)) with hs | hs
  · exact Or.inl hs
  rcases t.subset_compactSide_or_subset_endSide hconn
      (fun _ hx hf ↦ havoid hx (Or.inr hf)) with ht | ht
  · exact Or.inr ht
  exfalso
  let A := (K ∪ closure s.compactSide) ∪ closure t.compactSide
  have hAc : IsCompact A :=
    (hK.union s.isCompact_closure_compactSide).union t.isCompact_closure_compactSide
  have heK : range e ⊆ K := by
    intro x hx
    exact hK.isClosed.frontier_subset (hfront ▸ Or.inl hx)
  have hfK : range f ⊆ K := by
    intro x hx
    exact hK.isClosed.frontier_subset (hfront ▸ Or.inr hx)
  have hAeq : A = (K ∪ s.compactSide) ∪ t.compactSide := by
    dsimp [A]
    rw [s.closure_compactSide, t.closure_compactSide]
    aesop
  have hcA : c.range ⊆ A := by
    rw [hAeq]
    exact (c.range_subset_domain_union_compactSide s hc hs).trans subset_union_left
  have hdA : d.range ⊆ A := by
    rw [hAeq]
    intro x hx
    rcases d.range_subset_domain_union_compactSide t hd ht hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  have hAo : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rw [hAeq] at hx
    rcases hx with (hx | hx) | hx
    · by_cases hi : x ∈ interior K
      · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
          (interior_subset.trans (subset_union_left.trans subset_union_left))
      · have hf : x ∈ range e ∪ range f :=
          hfront ▸ (mem_frontier_iff_notMem_interior hx).mpr hi
        rcases hf with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact Filter.mem_of_superset
            (c.isOpen_range.mem_nhds ⟨(b, 0), c.zero_eq b⟩) hcA
        · exact Filter.mem_of_superset
            (d.isOpen_range.mem_nhds ⟨(b, 0), d.zero_eq b⟩) hdA
    · apply Filter.mem_of_superset (s.isOpen_compactSide.mem_nhds hx)
      rw [hAeq]
      exact subset_union_right.trans subset_union_left
    · apply Filter.mem_of_superset (t.isOpen_compactSide.mem_nhds hx)
      rw [hAeq]
      exact subset_union_right
  have hAuniv : A = univ := (show IsClopen A from ⟨hAc.isClosed, hAo⟩).eq_univ (by
    obtain ⟨x, hx⟩ := s.compactSide_nonempty
    exact ⟨x, Or.inl (Or.inr (subset_closure hx))⟩)
  apply s.not_isCompact_closure_endSide
  exact hAc.of_isClosed_subset isClosed_closure (hAuniv ▸ subset_univ _)

end Poincare.Topology.SphereSeparation
