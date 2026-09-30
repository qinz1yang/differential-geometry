import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ObservedHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctObservationNucleus

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Interface
namespace GC.TeamChecks
universe u

theorem sphere_zero_history_geometrizes : Geometrizes standardThreeSphereLift.{u} := by
  let M := standardThreeSphereLift.{u}
  let P := OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold
  let g : P.Metric := sphereLiftStructure.metric
  let K := HistoryEndpointInputs.atZero P g
  apply K.geometrizes M (InitialIdentification.reflAtZero P g)
  change ComponentsGeometrize P.toClosedOrientedManifold
  rw [OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold]
  exact (componentsGeometrize_iff M).mpr standardThreeSphereLift_geometrizes

theorem produced_raw_surgery_consumer
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric)
    (topology : ObservedTopologySupply (RawSurgery.ofInitial _ g).observation)
    (late : LateComponentSupply (RawSurgery.ofInitial _ g).observation) : Geometrizes M :=
  geometrizes_of_rawSurgery_supplies M (RawSurgery.ofInitial _ g) topology late

theorem terminal_history_consumer
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (H : ObservedHistory.{u}) (K : HistoryEndpointInputs H)
    (A : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H)
    (empty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) : Geometrizes M :=
  K.terminal M A empty

end GC.TeamChecks
