import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmallScaleNoncollapsingThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.LocalUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialRegularBlock

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem noncollapsing_through_surgery (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    NoncollapsingThroughSurgery P₀ g₀ :=
  noncollapsingThroughSurgery_of_reducedVolume_of_smallScale P₀ g₀
    (historyReducedVolumeMonotone_holds.{u}) (historyReducedVolumeLocalUpperBound_holds.{u})
    (historyReducedVolumeInitialLowerBound_holds P₀ g₀)
    (smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
