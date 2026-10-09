import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdFinalRM1
import DifferentialGeometry.Geometry.Collapse.GraphManifold

/-!
# Consumer of `exists_boundary_graph_threshold_final_RM1` (lane S-RIM81, G6)

The theorem is the admitted ledger input A01 `exists_boundary_graph_threshold`
(`Geometry/Collapse/GraphManifold.lean:116`) at universe `0`, with no hypothesis beyond its own
`K`, `hK`, `A`, `hA`. The first example restates the admitted statement VERBATIM (universe `0`, the
order hypothesis `staticDerivativeOrder ≤ K`) and proves it by the theorem; the second checks the
proof against the explicit original contract, without referring to the deleted declaration.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- The admitted statement `exists_boundary_graph_threshold` at universe `0`, verbatim, proved. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i :=
  exists_boundary_graph_threshold_final_RM1 K hK A hA

/-- The proof satisfies the explicit original boundary threshold contract at universe `0`. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  (exists_boundary_graph_threshold_final_RM1 K hK A hA :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i)

end DifferentialGeometry.Geometry.Collapse
