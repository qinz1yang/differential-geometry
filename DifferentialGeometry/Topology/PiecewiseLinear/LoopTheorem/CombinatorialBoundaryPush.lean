import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskPush
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryPush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_nonsingular_two_cell_in_combinatorial_manifold
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {D : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hDK : D ⊆ frontier K.space) :
    ∃ A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
      A.IsNonsingular ∧ A '' A.domain ⊆ K.space ∧
      Set.range A.boundary = r '' stdSimplexBoundary 2 ∧
      A '' A.domain ∩ frontier K.space = r '' stdSimplexBoundary 2 := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  have hbd := frontier_space_eq_boundaryComplex_space hK
  obtain ⟨Q, q, hq, hQK, hbound, hinter⟩ :=
    hK.exists_isPLHomeomorphOn_push_boundary_disk hr (hbd ▸ hDK)
  rw [← hbd] at hinter
  obtain ⟨A, hA, hAQ, hboundary⟩ := exists_nonsingular_two_cell_of_isPLBall hq
  exact ⟨A, hA, hAQ ▸ hQK, hboundary.trans hbound, hAQ ▸ hinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
