import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingFillingQuadrant

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem regular_closed_side_topology {E : Type*} [TopologicalSpace E] {X : Set E}
    (hX : IsClosed X) (hreg : closure (interior X) = X) (b : Bool) :
    IsClosed (if b then X else (interior X)ᶜ) ∧
      closure (interior (if b then X else (interior X)ᶜ)) =
        (if b then X else (interior X)ᶜ) ∧
      frontier (if b then X else (interior X)ᶜ) = frontier X := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨isOpen_interior.isClosed_compl, ?_, ?_⟩
    · rw [interior_compl, hreg, closure_compl]
    · rw [frontier_compl, frontier, interior_interior, hreg, frontier, hX.closure_eq]
  · exact ⟨hX, hreg, rfl⟩

theorem exists_closed_side_of_frontier_contact
    {E : Type*} [TopologicalSpace E] {R X : Set E} (hX : IsClosed X)
    (hregR : closure (interior R) = R) (hconnR : IsPreconnected (interior R))
    (hcontact : R ∩ frontier X ⊆ frontier R) :
    ∃ b : Bool, R ⊆ (if b then X else (interior X)ᶜ) := by
  rcases interior_subset_one_side_of_frontier_contact hX hregR hconnR hcontact with
    ⟨-, hin⟩ | ⟨-, hout⟩
  · exact ⟨true, hin⟩
  · refine ⟨false, ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, closure_compl] using hout

end DifferentialGeometry.Topology.PiecewiseLinear
