import DifferentialGeometry.Topology.ThreeManifold.Geometrization.FiniteConnectedSum
import DifferentialGeometry.Geometry.Thurston.Models.HomogeneousCompleteness

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry GC.Endpoint
open scoped Manifold ContDiff
namespace GC.TeamChecks

def nilGeometricStructure : GeometricStructure (𝓡 3) ModelCoordinates :=
  coordinateGeometricStructure .nil (by decide)

def solGeometricStructure : GeometricStructure (𝓡 3) ModelCoordinates :=
  coordinateGeometricStructure .sol (by decide)

example : nilGeometricStructure.metric = coordinateModelMetric .nil := rfl
example : solGeometricStructure.metric = coordinateModelMetric .sol := rfl

example : RiemannianMetricComplete (coordinateModelMetric .hyperbolic) :=
  coordinateModelMetric_complete .hyperbolic

def twoSphereCertificate :
    GeometrizationCertificate (connectedSum standardThreeSphereLift standardThreeSphereLift) :=
  sphereCertificate.connectedSum sphereCertificate

example : twoSphereCertificate.primeData.factors.length = 2 := rfl

example : Geometrizes (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold 3))) :=
  geometrizes_finiteConnectedSum [] (by simp)

theorem marked_family_consumer (M : ConnectedClosedOrientedManifold 3)
    (L : List (ConnectedClosedOrientedManifold 3))
    (h : ∀ P ∈ L, Geometrizes P) (f : MarkedFactorReconstruction M L) :
    Geometrizes M := geometrizes_of_markedFactors M L h f

end GC.TeamChecks
