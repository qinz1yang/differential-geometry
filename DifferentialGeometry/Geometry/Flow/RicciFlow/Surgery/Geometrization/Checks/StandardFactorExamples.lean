import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ClassifiedHistory

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint GC.Interface
namespace GC.TeamChecks
universe u

def antipodalCertificate : GeometrizationCertificate SphericalSpaceFormGroup.antipodal.manifold :=
  standardFactorCertificate _ (isStandardFactor_spherical _)

example : antipodalCertificate.primeData.factors = [SphericalSpaceFormGroup.antipodal.manifold] :=
  rfl

example (i : Fin antipodalCertificate.primeData.factors.length) :
    (antipodalCertificate.geometricFactors i).boundary.count = 0 :=
  standardFactorCertificate_no_tori _ _ i

theorem antipodal_endpoint_with_nontrivial_piOne :
    Geometrizes SphericalSpaceFormGroup.antipodal.manifold ∧
      ∀ p : SphericalSpaceFormGroup.antipodal.manifold.Carrier,
        ¬ Subsingleton (FundamentalGroup SphericalSpaceFormGroup.antipodal.manifold.Carrier p) :=
  ⟨⟨antipodalCertificate⟩, SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal⟩

theorem sphere_product_endpoint : Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u}) :=
  cycle_geometrizes_of_standard standardFactorEndpoints

def twoAntipodalCertificate : GeometrizationCertificate
    (connectedSum SphericalSpaceFormGroup.antipodal.manifold
      SphericalSpaceFormGroup.antipodal.manifold) :=
  antipodalCertificate.connectedSum antipodalCertificate

example : twoAntipodalCertificate.primeData.factors.length = 2 := rfl

theorem produced_raw_late_consumer
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric)
    (late : LateComponentSupply (RawSurgery.ofInitial _ g).observation) : Geometrizes M :=
  geometrizes_of_raw_late M (RawSurgery.ofInitial _ g) late

theorem produced_raw_terminal_consumer
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric)
    (b : ℝ) (hb : 0 ≤ b)
    (empty : IsEmpty (((RawSurgery.ofInitial _ g).observation.observe b hb).stage
      (Fin.last ((RawSurgery.ofInitial _ g).observation.observe b hb).eventCount)).Carrier) :
    Geometrizes M := geometrizes_of_raw_empty M (RawSurgery.ofInitial _ g) b hb empty

end GC.TeamChecks
