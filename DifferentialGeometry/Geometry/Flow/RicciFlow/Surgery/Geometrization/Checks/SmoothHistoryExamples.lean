import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.RawHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.Checks.ConnectedSumExamples
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctObservationNucleus

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Interface
namespace GC.TeamChecks
universe u

example : twoSphereCertificate.opposite.primeData.factors.length = 2 := by
  rw [GeometrizationCertificate.opposite_factor_count]
  rfl

theorem opposite_sphere_zero_history_geometrizes :
    Geometrizes standardThreeSphereLift.{u}.opposite := by
  let M := standardThreeSphereLift.{u}.opposite
  let P := OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold
  let g : P.Metric := sphereLiftStructure.metric
  apply geometrizes_of_smooth_history M (ObservedHistory.atZero P g)
    (InitialIdentification.reflAtZero P g)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  change ComponentsGeometrize P.toClosedOrientedManifold
  rw [OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold]
  exact (componentsGeometrize_iff M).mpr ⟨sphereCertificate.opposite⟩

theorem produced_raw_smooth_consumer
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric)
    (standard : StandardFactorEndpoints.{u})
    (late : LateComponentSupply (RawSurgery.ofInitial _ g).observation) : Geometrizes M :=
  geometrizes_of_raw_standard_late M (RawSurgery.ofInitial _ g) standard late

theorem raw_terminal_smooth_consumer
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (standard : StandardFactorEndpoints.{u}) (b : ℝ) (hb : 0 ≤ b)
    (empty : IsEmpty ((F.observation.observe b hb).stage
      (Fin.last (F.observation.observe b hb).eventCount)).Carrier) : Geometrizes M :=
  geometrizes_of_raw_terminal M F standard b hb empty

end GC.TeamChecks
