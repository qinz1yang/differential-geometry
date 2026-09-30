import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.LocalUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialRegularBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.UniformEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Pinching.ThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.Continuation
set_option autoImplicit false
noncomputable section
open scoped Manifold
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem general_noncollapsing_of_small_scale
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hsmall : SmallScaleNoncollapsingThroughSurgery P g) :
    NoncollapsingThroughSurgery P g :=
  noncollapsingThroughSurgery_of_reducedVolume_of_smallScale P g
    (historyReducedVolumeMonotone_holds.{u}) (historyReducedVolumeLocalUpperBound_holds.{u})
    (historyReducedVolumeInitialLowerBound_holds P g) hsmall

theorem general_strong_canonical_of_small_scale
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hsmall : SmallScaleNoncollapsingThroughSurgery P g) :
    CanonicalNeighborhoodsThroughSurgeryStrong P g :=
  canonicalNeighborhoodsThroughSurgeryStrong_of_leaves P g
    (pinchingThroughSurgery P g) (general_noncollapsing_of_small_scale P g hsmall)
    (canonical_neighborhood_continuation P g) (spatial_canonical_continuation P g)

end GC.GeneralFlow
