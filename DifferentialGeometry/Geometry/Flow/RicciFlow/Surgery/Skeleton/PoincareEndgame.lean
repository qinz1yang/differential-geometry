import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PinchingThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DeepContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NoncollapsingThroughSurgeryLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodsThroughSurgeryStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmallScaleNoncollapsingThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedVolumeMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedVolumeLocalUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialRegularBlock


set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem uniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ := by
  sorry

theorem historyReducedVolumeMonotone (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeMonotone P₀ :=
  historyReducedVolumeMonotone_holds P₀

theorem historyReducedVolumeLocalUpperBound (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeLocalUpperBound P₀ :=
  historyReducedVolumeLocalUpperBound_holds P₀

theorem historyReducedVolumeInitialLowerBound (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    HistoryReducedVolumeInitialLowerBound P₀ g₀ :=
  historyReducedVolumeInitialLowerBound_holds P₀ g₀

theorem smallScaleNoncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    SmallScaleNoncollapsingThroughSurgery P₀ g₀ :=
  smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀

theorem noncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier]
    (g₀ : P₀.Metric) :
    NoncollapsingThroughSurgery P₀ g₀ :=
  noncollapsingThroughSurgery_of_reducedVolume_of_smallScale P₀ g₀
    (historyReducedVolumeMonotone P₀) (historyReducedVolumeLocalUpperBound P₀)
    (historyReducedVolumeInitialLowerBound P₀ g₀) (smallScaleNoncollapsingThroughSurgery P₀ g₀)

theorem crossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CrossingContinuation P₀ g₀ :=
  crossingContinuation_holds P₀ g₀

theorem canonicalNeighborhoodContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CanonicalNeighborhoodContinuation P₀ g₀ :=
  canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing P₀ g₀
    (deepContinuation P₀ g₀) (capWindowContinuation P₀ g₀) (crossingContinuation P₀ g₀)

theorem spatialCanonicalContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCanonicalContinuation P₀ g₀ := by
  sorry

theorem canonicalNeighborhoodsThroughSurgeryStrong (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀ :=
  canonicalNeighborhoodsThroughSurgeryStrong_of_leaves P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (noncollapsingThroughSurgery P₀ g₀)
    (canonicalNeighborhoodContinuation P₀ g₀) (spatialCanonicalContinuation P₀ g₀)

theorem smoothPoincareConjecture_holds : smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_uniformDebitSurgeryStepStrong_of_canonicalNeighborhoodsStrong
    uniformDebitSurgeryStepStrong canonicalNeighborhoodsThroughSurgeryStrong

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
