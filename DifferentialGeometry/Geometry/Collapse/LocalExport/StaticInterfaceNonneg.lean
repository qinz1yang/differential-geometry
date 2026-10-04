import DifferentialGeometry.Geometry.Collapse.LocalExport.StaticInterfaceBoundary
import DifferentialGeometry.Geometry.Thurston.NonnegativeClassificationUnconditional

/-!
# LC90, static side: the nonnegative branch discharged by the classification

Blueprint row LC90 (`prop:collapse-static-flow-interface`, master207A) takes as input (4) "the
separate nonnegative-component data". `LocalExport/StaticInterfaceBoundary.lean`
(`HyperbolicOrCollapsed.nonempty_hyperbolicOrGraph`) takes the nonnegative branch as an explicit
input in raw-graph form, because the tree's raw recognitions
`rawGraphPresentation_of_{sphericalSpaceForm,sphericalProduct,flat}` are still admitted. The closed
nonnegative classification is now unconditional
(`closed_nonnegative_sectional_classification_unconditional`, PORT567b). This module uses it to
discharge input (4) with no assumption: a closed nonnegatively curved piece is sent to its own
geometric branch (spherical, `S² × ℝ` or Euclidean structure), as LC90's proof says ("a component
with curvature scale `+∞` needs its explicit nonnegative-curvature/classification branch").

* `HyperbolicOrCollapsed.hyperbolicOrGraph_or_closedGeometric`: with the static theorem at
  `(K, A, w₀)` as the only explicit input (lead's interface form), every piece is hyperbolic or
  carries a raw graph presentation, or is closed with a spherical, `S² × ℝ` or Euclidean geometric
  structure.
* `HyperbolicOrCollapsed.nonempty_hyperbolicOrGraph_of_boundary_nonempty`: a piece with nonempty
  boundary is hyperbolic or a raw graph, given the static theorem only.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **LC90, componentwise step with the nonnegative branch discharged.** Given the static theorem
at `(K, A, w₀)`, every piece of a torus decomposition that is hyperbolic, collapsed or closed and
nonnegatively curved is hyperbolic or carries a raw graph presentation, or is closed with a
spherical, `S² × ℝ` or Euclidean geometric structure (unconditional classification). -/
theorem HyperbolicOrCollapsed.hyperbolicOrGraph_or_closedGeometric
    {M : ConnectedClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    {D : TorusDecomposition M} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ} {i : Fin D.components.count}
    (piece : HyperbolicOrCollapsed g D K A w₀ i)
    (collapse : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V)) :
    Nonempty (HyperbolicOrGraph D.carrier D.components i) ∨
      ((D.component i).model.boundary (D.component i).Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure (D.component i).model (D.component i).Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  have : ConnectedSpace (D.component i).Carrier := D.components.connected i
  cases piece with
  | hyperbolic geometry model_eq => exact Or.inl ⟨.hyperbolic geometry model_eq⟩
  | collapsed h _ hh =>
    obtain ⟨G⟩ := collapse (D.component i) h hh
    exact Or.inl ⟨.graph G⟩
  | nonnegative h _ hclosed hcurvature =>
    exact Or.inr ⟨hclosed, GC.Geometry.closed_nonnegative_sectional_classification_unconditional
      (D.component i) h hclosed hcurvature⟩

/-- A piece with nonempty boundary is hyperbolic or carries a raw graph presentation, given only
the static theorem at `(K, A, w₀)`. -/
theorem HyperbolicOrCollapsed.nonempty_hyperbolicOrGraph_of_boundary_nonempty
    {M : ConnectedClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    {D : TorusDecomposition M} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ} {i : Fin D.components.count}
    (piece : HyperbolicOrCollapsed g D K A w₀ i)
    (collapse : ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
      (h : SmoothRiemannianMetric V.model V.Carrier),
      staticCollapseHypotheses V h K A w₀ → Nonempty (RawGraphPresentation V))
    (hbd : ((D.component i).model.boundary (D.component i).Carrier).Nonempty) :
    Nonempty (HyperbolicOrGraph D.carrier D.components i) :=
  (piece.hyperbolicOrGraph_or_closedGeometric collapse).resolve_right
    fun h => hbd.ne_empty h.1

end DifferentialGeometry.Geometry.Collapse
