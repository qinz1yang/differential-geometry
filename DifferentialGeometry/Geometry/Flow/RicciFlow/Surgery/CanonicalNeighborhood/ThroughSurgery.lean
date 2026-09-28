import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.UniformEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Pinching.ThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.Continuation

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem canonical_neighborhoods_through_surgery (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀ :=
  canonicalNeighborhoodsThroughSurgeryStrong_of_leaves P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (noncollapsing_through_surgery P₀ g₀)
    (canonical_neighborhood_continuation P₀ g₀) (spatial_canonical_continuation P₀ g₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
