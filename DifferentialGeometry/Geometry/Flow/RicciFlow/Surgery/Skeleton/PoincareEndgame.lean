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
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuationCases
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFineCutNeckSupplyStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyStrongLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongNecksOfCutoffClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf


set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem fineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ :=
  fineCutNeckSupplyStrong_holds P₀ g₀

theorem strongNecksOfCutoffClass (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ :=
  strongNecksOfCutoffClass_of_strongSpatialCrossing P₀ g₀
    (strongSpatialCrossingContinuation_holds P₀ g₀)

theorem uniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ :=
  uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (strongNecksOfCutoffClass P₀ g₀) (fineCutNeckSupplyStrong P₀ g₀)

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

theorem spatialCrossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCrossingContinuation P₀ g₀ :=
  spatialCrossingContinuation_holds P₀ g₀

theorem spatialCanonicalContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCanonicalContinuation P₀ g₀ :=
  spatialCanonicalContinuation_of_spatialCrossing P₀ g₀ (spatialCrossingContinuation P₀ g₀)

theorem canonicalNeighborhoodsThroughSurgeryStrong (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀ :=
  canonicalNeighborhoodsThroughSurgeryStrong_of_leaves P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (noncollapsingThroughSurgery P₀ g₀)
    (canonicalNeighborhoodContinuation P₀ g₀) (spatialCanonicalContinuation P₀ g₀)

theorem exists_poincare_controlled_extinction
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier]
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    Nonempty (PoincareControlledExtinction M g) := by
  have : SimplyConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold M).Carrier :=
    inferInstanceAs (SimplyConnectedSpace M.Carrier)
  exact exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong
    (OrientedThreeStage.ofClosedOrientedManifold M) g
    (uniformDebitSurgeryStepStrong (OrientedThreeStage.ofClosedOrientedManifold M) g)
    (canonicalNeighborhoodsThroughSurgeryStrong (OrientedThreeStage.ofClosedOrientedManifold M) g)

theorem smoothPoincareConjecture_holds
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨f⟩ := smoothPoincareConjecture_of_controlledExtinction
    (fun N _ g => exists_poincare_controlled_extinction N.toClosedOrientedManifold g) M
  exact ⟨f.trans DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
