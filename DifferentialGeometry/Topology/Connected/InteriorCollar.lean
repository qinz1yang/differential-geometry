import Mathlib.Topology.Connected.Basic

open Set

namespace DifferentialGeometry.Topology

theorem isPreconnected_interior_of_frontier_nhds {X : Type*} [TopologicalSpace X] {K C : Set X}
    (hK : IsPreconnected K) (hreg : closure (interior K) = K)
    (hC : IsPreconnected C) (hCK : C ⊆ interior K)
    (hloc : ∀ p ∈ frontier K, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ U ∩ interior K ⊆ C) :
    IsPreconnected (interior K) := by
  intro u v hu hv hcover hsu hsv
  by_contra hempty
  have hdisj : ∀ y ∈ interior K, y ∈ u → y ∈ v → False := fun y hy hyu hyv =>
    hempty ⟨y, hy, hyu, hyv⟩
  set A := interior K ∩ u
  set B := interior K ∩ v
  have hAB : interior K ⊆ A ∪ B := fun y hy =>
    (hcover hy).imp (fun h => ⟨hy, h⟩) (fun h => ⟨hy, h⟩)
  have hKcover : K ⊆ closure A ∪ closure B := by
    rw [← hreg, ← closure_union]
    exact closure_mono hAB
  have hsep : ∀ p ∈ K, p ∈ closure A → p ∈ closure B → False := by
    intro p hpK hpA hpB
    by_cases hpint : p ∈ interior K
    · rcases hcover hpint with hpu | hpv
      · obtain ⟨y, ⟨hy, hyu⟩, -, hyv⟩ := mem_closure_iff.mp hpB (interior K ∩ u)
          (isOpen_interior.inter hu) ⟨hpint, hpu⟩
        exact hdisj y hy hyu hyv
      · obtain ⟨y, ⟨hy, hyv⟩, -, hyu⟩ := mem_closure_iff.mp hpA (interior K ∩ v)
          (isOpen_interior.inter hv) ⟨hpint, hpv⟩
        exact hdisj y hy hyu hyv
    · have hpf : p ∈ frontier K := ⟨subset_closure hpK, hpint⟩
      obtain ⟨U, hU, hpU, hUC⟩ := hloc p hpf
      obtain ⟨a, haU, haK, hau⟩ := mem_closure_iff.mp hpA U hU hpU
      obtain ⟨b, hbU, hbK, hbv⟩ := mem_closure_iff.mp hpB U hU hpU
      obtain ⟨y, hyC, hyu, hyv⟩ := hC u v hu hv (hCK.trans hcover) ⟨a, hUC ⟨haU, haK⟩, hau⟩
        ⟨b, hUC ⟨hbU, hbK⟩, hbv⟩
      exact hdisj y (hCK hyC) hyu hyv
  obtain ⟨a, haK, hau⟩ := hsu
  obtain ⟨b, hbK, hbv⟩ := hsv
  obtain ⟨p, hpK, hpA, hpB⟩ := isPreconnected_closed_iff.mp hK _ _ isClosed_closure
    isClosed_closure hKcover ⟨a, interior_subset haK, subset_closure ⟨haK, hau⟩⟩
    ⟨b, interior_subset hbK, subset_closure ⟨hbK, hbv⟩⟩
  exact hsep p hpK hpA hpB

end DifferentialGeometry.Topology
