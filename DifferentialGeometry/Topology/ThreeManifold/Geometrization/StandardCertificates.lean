import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes
import DifferentialGeometry.Geometry.Thurston.StandardFactorGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.SmoothReconstruction

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

def primeGeometricCertificate (P : ConnectedClosedOrientedManifold.{u} 3)
    (hp : IsPrime P) (G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) :
    GeometrizationCertificate P where
  primeData := {
    factors := [P]
    factors_nonempty := by simp
    prime := by intro Q hQ; simpa only [List.mem_singleton.mp hQ] using hp
    reconstruction := ClosedOrientedManifold.OrientedDiffeomorph.refl _ }
  geometricFactors i := by simpa using NoCuts.geometricDecomposition P G

def elementaryGeometricStructure (P : ConnectedClosedOrientedManifold.{u} 3)
    (k : GC.Geometry.ElementaryModel) (g : SmoothRiemannianMetric (𝓡 3) P.Carrier)
    (hg : GC.Geometry.ElementaryGeometry g k) : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier := by
  cases k with
  | spherical => exact ⟨.spherical, g, hg.1, hg.2, by intro h; cases h⟩
  | euclidean => exact ⟨.euclidean, g, hg.1, hg.2, by intro h; cases h⟩
  | sphericalProduct => exact ⟨.sphericalProduct, g, hg.1, hg.2, by intro h; cases h⟩

def standardFactorCertificate (P : ConnectedClosedOrientedManifold.{u} 3)
    (hP : isStandardFactor P) : GeometrizationCertificate P :=
  let h := GC.Geometry.standard_factor_complete_geometry P hP
  primeGeometricCertificate P (isPrime_of_isStandardFactor P hP)
    (elementaryGeometricStructure P h.choose h.choose_spec.choose h.choose_spec.choose_spec)

theorem standardFactorCertificate_factors (P : ConnectedClosedOrientedManifold.{u} 3)
    (hP : isStandardFactor P) : (standardFactorCertificate P hP).primeData.factors = [P] := rfl

theorem standardFactorCertificate_no_tori (P : ConnectedClosedOrientedManifold.{u} 3)
    (hP : isStandardFactor P) (i : Fin (standardFactorCertificate P hP).primeData.factors.length) :
    ((standardFactorCertificate P hP).geometricFactors i).boundary.count = 0 := by
  fin_cases i
  rfl

theorem standardFactorEndpoints : StandardFactorEndpoints.{u} :=
  fun P hP => ⟨standardFactorCertificate P hP⟩

theorem geometrizes_of_isStandardFactor (P : ConnectedClosedOrientedManifold.{u} 3)
    (h : isStandardFactor P) : Geometrizes P := standardFactorEndpoints P h

theorem geometrizes_of_isPoincareStandard (P : ConnectedClosedOrientedManifold.{u} 3)
    (h : isPoincareStandard P.Carrier) : Geometrizes P :=
  geometrizes_of_poincareStandard standardFactorEndpoints P h

end GC.Endpoint
