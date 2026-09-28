import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongNecksOfCutoffClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem strong_necks_of_cutoff_class (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ :=
  strongNecksOfCutoffClass_of_strongSpatialCrossing P₀ g₀
    (strongSpatialCrossingContinuation_holds P₀ g₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
