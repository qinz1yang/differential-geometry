import Mathlib.Topology.Connected.Clopen

open Set

namespace Poincare.Topology

theorem cover_and_between_subset_of_frontier_sections
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (P D Q A B : Set X)
    (hP : frontier P ⊆ A) (hD : frontier D ⊆ A ∪ B) (hQ : frontier Q ⊆ B)
    (hAD : A ⊆ D) (hBD : B ⊆ D)
    (hleft : A ⊆ interior (P ∪ D)) (hright : B ⊆ interior (D ∪ Q))
    (hne : (P ∪ D ∪ Q).Nonempty) :
    P ∪ D ∪ Q = univ ∧ (interior P)ᶜ ∩ (interior Q)ᶜ ⊆ D := by
  have hA : A ⊆ interior (P ∪ D ∪ Q) :=
    hleft.trans (interior_mono subset_union_left)
  have hB : B ⊆ interior (P ∪ D ∪ Q) := by
    apply hright.trans (interior_mono ?_)
    intro x hx
    exact hx.elim (fun hd ↦ Or.inl (Or.inr hd)) Or.inr
  have hfront : frontier (P ∪ D ∪ Q) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hs : x ∈ A ∪ B := by
      rcases frontier_union_subset (P ∪ D) Q hx with hpd | hq
      · rcases frontier_union_subset P D hpd.1 with hp | hd
        · exact Or.inl (hP hp.1)
        · exact hD hd.2
      · exact Or.inr (hQ hq.2)
    exact hx.2 (hs.elim (fun ha ↦ hA ha) (fun hb ↦ hB hb))
  have hcover := (isClopen_iff_frontier_eq_empty.mpr hfront).eq_univ hne
  refine ⟨hcover, ?_⟩
  intro x hx
  rcases (show x ∈ P ∪ D ∪ Q from hcover.symm ▸ mem_univ x) with (hp | hd) | hq
  · exact hAD (hP ⟨subset_closure hp, hx.1⟩)
  · exact hd
  · exact hBD (hQ ⟨subset_closure hq, hx.2⟩)

end Poincare.Topology
