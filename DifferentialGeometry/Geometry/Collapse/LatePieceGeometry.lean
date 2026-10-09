import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Refinement

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Collapse
universe u

def cutPieceMap {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count) :
    (D.component i).Carrier → M.Carrier :=
  fun x => D.reconstruction.val (D.boundary.quotientMap x.val)

def isInducedCutMetric {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier) : Prop :=
  ∀ (x : (D.component i).Carrier) (v w : TangentSpace (D.component i).model x),
    h.inner x v w = g.inner (cutPieceMap D i x)
      (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) x v)
      (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) x w)

inductive HyperbolicOrCollapsed {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ)
    (i : Fin D.components.count)
  | hyperbolic (geometry : D.carrier.InteriorGeometry (D.components.piece i))
      (model_eq : isHyperbolicInteriorGeometry geometry)
  | collapsed
      (metric : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
      (induced : isInducedCutMetric g D i metric)
      (hypotheses : staticCollapseHypotheses (D.component i) metric K A w₀)
  | nonnegative
      (metric : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
      (induced : isInducedCutMetric g D i metric)
      (closed : (D.component i).model.boundary (D.component i).Carrier = ∅)
      (curvature : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow metric 0)

end DifferentialGeometry.Geometry.Collapse
