import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardCertificates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.RawHistory

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Interface
namespace GC.Endpoint
universe u

theorem geometrizes_of_raw_final_components
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (b : ℝ) (hb : 0 ≤ b)
    (final : ComponentsGeometrize
      ((F.observation.observe b hb).stage
        (Fin.last (F.observation.observe b hb).eventCount)).toClosedOrientedManifold) :
    Geometrizes M :=
  geometrizes_of_raw_observation M F standardFactorEndpoints b hb final

theorem geometrizes_of_raw_empty
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (b : ℝ) (hb : 0 ≤ b)
    (empty : IsEmpty ((F.observation.observe b hb).stage
      (Fin.last (F.observation.observe b hb).eventCount)).Carrier) : Geometrizes M :=
  geometrizes_of_raw_terminal M F standardFactorEndpoints b hb empty

theorem geometrizes_of_raw_late
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (late : LateComponentSupply F.observation) : Geometrizes M :=
  geometrizes_of_raw_standard_late M F standardFactorEndpoints late

end GC.Endpoint
