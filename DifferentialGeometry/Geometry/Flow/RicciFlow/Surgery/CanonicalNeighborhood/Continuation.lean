import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DeepContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuationCases
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem canonical_neighborhood_continuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CanonicalNeighborhoodContinuation P₀ g₀ :=
  canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing P₀ g₀
    (deepContinuation P₀ g₀) (capWindowContinuation P₀ g₀) (crossingContinuation_holds P₀ g₀)

theorem spatial_canonical_continuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCanonicalContinuation P₀ g₀ :=
  spatialCanonicalContinuation_of_spatialCrossing P₀ g₀ (spatialCrossingContinuation_holds P₀ g₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
