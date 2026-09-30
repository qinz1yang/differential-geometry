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

theorem geometrizes_of_hyperbolicOrCollapsed
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ)
    (collapse : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (h : SmoothRiemannianMetric W.model W.Carrier),
      staticCollapseHypotheses W h K A w₀ → Nonempty (RawGraphPresentation W))
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : (i : Fin D.components.count) → HyperbolicOrCollapsed g D K A w₀ i) :
    Geometrizes M := by
  apply geometrizes_of_hyperbolicOrGraph M D incompressible
  intro i
  have : ConnectedSpace (D.component i).Carrier := D.components.connected i
  cases pieces i with
  | hyperbolic h hh => exact .hyperbolic h hh
  | collapsed h _ hh =>
    exact .graph (Classical.choice
      (collapse (D.component i) h hh))
  | nonnegative h _ hclosed hcurvature =>
    exact .graph (Classical.choice
      (exists_rawGraphPresentation_of_nonnegative (D.component i) h hclosed hcurvature))

end DifferentialGeometry.Geometry.Collapse
