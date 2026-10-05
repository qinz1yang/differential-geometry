import Mathlib.Topology.Neighborhoods

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_sdiff_eq_closure_interior_sdiff {P C : Set X}
    (hP : closure (interior P) = P) (hC : IsClosed C) :
    closure (P \ C) = closure (interior P \ C) := by
  apply Subset.antisymm _ (closure_mono (sdiff_subset_sdiff_left interior_subset))
  apply closure_minimal _ isClosed_closure
  simpa only [hP, hC.closure_eq] using (closure_sdiff (s := interior P) (t := C))

theorem closure_interior_closure_sdiff {P C : Set X}
    (hP : closure (interior P) = P) (hC : IsClosed C) :
    closure (interior (closure (P \ C))) = closure (P \ C) := by
  rw [closure_sdiff_eq_closure_interior_sdiff hP hC]
  apply Subset.antisymm (closure_minimal interior_subset isClosed_closure)
  exact closure_mono (interior_maximal subset_closure (isOpen_interior.sdiff hC))

theorem interior_closure_sdiff_subset_compl {P C : Set X}
    (hC : closure (interior C) = C) : interior (closure (P \ C)) ⊆ Cᶜ := by
  have hsub : closure (P \ C) ⊆ (interior C)ᶜ :=
    closure_minimal (fun _ hx hy => hx.2 (interior_subset hy)) isOpen_interior.isClosed_compl
  have h := interior_mono hsub
  rwa [interior_compl, hC] at h

theorem closure_inter_sdiff_eq_inter_closure_sdiff {P C Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) (hC : closure (interior C) = C)
    (hreg : closure (interior (closure (P \ C) ∩ Q)) = closure (P \ C) ∩ Q) :
    closure ((P ∩ Q) \ (C ∩ Q)) = closure (P \ C) ∩ Q := by
  apply Subset.antisymm
  · apply closure_minimal _ (isClosed_closure.inter hQ)
    rintro x ⟨⟨hxP, hxQ⟩, hxC⟩
    exact ⟨subset_closure ⟨hxP, fun hx => hxC ⟨hx, hxQ⟩⟩, hxQ⟩
  · rw [← hreg]
    apply closure_mono
    intro x hx
    have hxR : x ∈ interior (closure (P \ C)) := interior_mono inter_subset_left hx
    have hxQ : x ∈ Q := (interior_subset hx).2
    exact ⟨⟨closure_minimal sdiff_subset hP (interior_subset hxR), hxQ⟩,
      fun hxC => interior_closure_sdiff_subset_compl hC hxR hxC.1⟩
end DifferentialGeometry.Topology
