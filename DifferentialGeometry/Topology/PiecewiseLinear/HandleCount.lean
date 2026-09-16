import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryEuler
import DifferentialGeometry.Topology.PiecewiseLinear.BettiPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodHomology
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open Classical in
theorem IsOrientable.derivedNeighborhood {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (h : IsOrientable (n + 1) K) :
    IsOrientable (n + 1) (derivedNeighborhood K L) := by
  have hK'' := hK.secondDerived
  have hN := hK.derivedNeighborhood L
  exact IsOrientable.of_le (secondDerived K)
    (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L)
    (derivedNeighborhood_faces_subset K L) hK'' hN
    (h.barycentricSubdivision hK |>.barycentricSubdivision hK.barycentricSubdivision)

open Classical in
theorem eulerChar_boundary_derivedNeighborhood_eq_two_mul [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces) :
    eulerChar (boundaryComplex 3 (derivedNeighborhood K L)) = 2 * eulerChar L := by
  rw [eulerChar_boundaryComplex_eq_two_mul (derivedNeighborhood K L) (hK.derivedNeighborhood L),
    eulerChar_derivedNeighborhood_eq hL]

open Classical in
theorem bettiOne_derivedNeighborhood_graph
    [Finite L.faces]
    (hL : L.faces ⊆ K.faces) (hd : ∀ s ∈ L.faces, s.card ≤ 2)
    (hconn : IsConnected L.space) :
    (Homology.bettiOne (derivedNeighborhood K L).space : ℤ) = 1 - eulerChar L := by
  rw [bettiOne_derivedNeighborhood_eq hL]
  exact bettiOne_graph L hd hconn

end DifferentialGeometry.Topology.PiecewiseLinear
