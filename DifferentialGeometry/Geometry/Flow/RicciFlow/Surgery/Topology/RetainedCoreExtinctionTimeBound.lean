import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ExtinctionTimeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreUniformRecords

set_option autoImplicit false

noncomputable section

open scoped Topology Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound
    {M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3}
    [SimplyConnectedSpace M.Carrier]
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b),
      HistoryScalarLowerBound (T.toObservationTower.observe b hb.le) c) :
    hasExtinctObservationTower M g :=
  letI : ConnectedSpace
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Carrier :=
    M.connected
  letI : SimplyConnectedSpace
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Carrier :=
    inferInstanceAs (SimplyConnectedSpace M.Carrier)
  (T.toObservationTower.uniformRecordsAbove_of_scalarLowerBound parameters cutoff hc hscalar).elim
    fun _ h =>
      hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove M g T hbfr hctrl h

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_scalarLowerBound
    {M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3}
    [SimplyConnectedSpace M.Carrier]
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b),
      HistoryScalarLowerBound (T.toObservationTower.observe b hb.le) c) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_extinctObservationTower M g
    (hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound T hbfr hctrl parameters
      cutoff hc hscalar)

end DifferentialGeometry.PDE.RicciFlow.Surgery
