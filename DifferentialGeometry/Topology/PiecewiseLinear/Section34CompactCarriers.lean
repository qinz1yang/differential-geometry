import DifferentialGeometry.Topology.PiecewiseLinear.SmallBallNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_section34CompactCarrierControl (K : Geometry.SimplicialComplex ℝ E3)
    {h : E3 → E3} {ε : ℝ} (hε : 0 < ε) {X : Finset E3 → Set E3}
    (hX : ∀ t ∈ K.faces, h '' section34CompactCarrierSupport K t ⊆ X t)
    (hXb : ∀ t ∈ K.faces, Bornology.IsBounded (X t))
    (hXd : ∀ t ∈ K.faces, Metric.diam (X t) < ε / 4) :
    ∃ H : Finset E3 → Set E3, Section34CompactCarrierControl K h ε H ∧
      ∀ t ∈ K.faces, X t ⊆ interior (H t) := by
  have hex : ∀ t : Finset E3, ∃ Ht : Set E3, t ∈ K.faces →
      IsPLCellOn 3 Ht (frontier Ht) ∧ X t ⊆ interior Ht ∧ ∀ y ∈ Ht, ∀ z ∈ Ht, dist y z < ε := by
    intro t
    by_cases ht : t ∈ K.faces
    · obtain ⟨Ht, hHt⟩ := exists_isPLCellOn_frontier_subset_interior_of_diam_lt (hXb t ht) hε
        (hXd t ht)
      exact ⟨Ht, fun _ => hHt⟩
    · exact ⟨∅, fun h' => absurd h' ht⟩
  choose H hH using hex
  exact ⟨H, ⟨fun t ht => (hX t ht).trans (hH t ht).2.1, fun t ht => (hH t ht).2.2,
    fun t ht => (hH t ht).1⟩, fun t ht => (hH t ht).2.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
