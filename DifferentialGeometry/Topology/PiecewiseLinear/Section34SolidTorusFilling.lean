import DifferentialGeometry.Topology.SolidTorus.Embedded
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionRegions
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.Connected.CompactRegion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalSolidTorus.isConnected_compl_of_combinatorial_manifold
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hT : IsTopologicalSolidTorus K.space)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) : IsConnected K.spaceᶜ := by
  exact (isConnected_interior_space_and_compl (Set.toFinite K.faces) hK
    (hT.isConnected_frontier (isPolyhedron_space K).isClosed) hT.interior_nonempty).2.1

theorem IsTopologicalSolidTorus.exists_isPLBall_subset_of_sphere
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hT : IsTopologicalSolidTorus K.space)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S) (hST : S ⊆ K.space) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 B ∧ frontier B = S ∧ B ⊆ K.space := by
  obtain ⟨B, hB, hfront, -⟩ := hS.exists_isPLBall_frontier_eq
  refine ⟨B, hB, hfront, ?_⟩
  exact DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    hB.isPolyhedron.isCompact (isPolyhedron_space K).isCompact
    (hT.isConnected_compl_of_combinatorial_manifold hK).isPreconnected (hfront ▸ hST)

end DifferentialGeometry.Topology.PiecewiseLinear
