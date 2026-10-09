import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereExample
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Statement
import DifferentialGeometry.Geometry.Thurston.Atlas

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff
namespace GC.TeamChecks
open GC.Geometry

def euclideanGeometricStructure : GeometricStructure (𝓡 3) ModelCoordinates where
  model := .euclidean
  metric := euclideanModelMetric
  complete := euclideanModel_complete
  atlas := ModelAtlas.refl _
  hyperbolic_finite_volume := by intro h; cases h

theorem no_ninth_model : Fintype.card ThurstonModel = 8 := ThurstonModel.card

theorem nil_cross_term (p v : ModelCoordinates) :
    coordinateCoframe .nil p v 2 = v 2 - p 0 * v 1 := rfl

theorem sl2_cross_term (p v : ModelCoordinates) :
    coordinateCoframe .universalSL2 p v 2 = v 2 + Real.exp (-p 1) * v 0 := rfl

open DifferentialGeometry.Topology GC.Endpoint

theorem certificate_has_factor {M : ConnectedClosedOrientedManifold 3}
    (C : GeometrizationCertificate M) :
    ∃ i : Fin C.primeData.factors.length,
      GC.Endpoint.IsPrime (C.primeData.factors.get i) ∧
      Nonempty (GeometricDecomposition (C.primeData.factors.get i)) := by
  obtain ⟨i⟩ := C.primeData.factor_index_nonempty
  exact ⟨i, C.primeData.prime _ (List.get_mem _ _), ⟨C.geometricFactors i⟩⟩

theorem cut_interior_separates {C : CompactCarrier} (G : TorusGluing C)
    (x : C.interior) (y : C.Carrier) (h : G.quotientMap x.val = G.quotientMap y) :
    x.val = y := G.interior_fiber_singleton x.property h

example : Geometrizes standardThreeSphereLift := standardThreeSphereLift_geometrizes

example : sphereCertificate.primeData.factors.length = 1 := rfl

example : (NoCuts.geometricDecomposition standardThreeSphereLift sphereLiftStructure).boundary.count = 0 := rfl

example : (NoCuts.geometricDecomposition standardThreeSphereLift sphereLiftStructure).components.count = 1 := rfl

end GC.TeamChecks
