import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Geometry.Thurston.SphericalProductRawRecognition

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff
namespace GC.GraphManifold
universe u


theorem rawGraphPresentation_of_sphericalProduct
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hboundary : W.model.boundary W.Carrier = ∅)
    (G : GC.Geometry.GeometricStructure W.model W.Carrier)
    (hG : G.model = .sphericalProduct) : Nonempty (RawGraphPresentation W) := by
  exact rawGraphPresentation_of_sphericalProduct_proved W hboundary G hG


end GC.GraphManifold
