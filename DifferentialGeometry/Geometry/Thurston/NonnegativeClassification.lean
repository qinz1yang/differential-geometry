import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Compat.Ch567.Geometry.Thurston.NonnegativeClassificationImport

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff
namespace GC.Geometry
universe u

theorem closed_nonnegative_sectional_classification
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (hboundary : W.model.boundary W.Carrier = ∅)
    (hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :
    ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
      G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean :=
  closed_nonnegative_sectional_classification_unconditional W g hboundary hsec

end GC.Geometry
