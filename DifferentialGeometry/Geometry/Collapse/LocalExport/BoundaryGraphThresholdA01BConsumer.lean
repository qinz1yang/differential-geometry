import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdA01B
import DifferentialGeometry.Geometry.Collapse.GraphManifold

/-!
# Consumer of `exists_boundary_graph_threshold_of_rim_hint_A01B` (lane S-A01BMAP, `_A01B`)

The conclusion of the theorem is, up to its single hypothesis `hrimint` (the pair `hrim ∧ hint` of
`boundary_strongCertificate_V32_A4_OBDf`), the type of the admitted ledger input A01
`exists_boundary_graph_threshold` at universe `0`: the examples check the explicit original contract
with the order hypothesis `10 ≤ K` against `staticDerivativeOrder ≤ K` and the
positivity hypothesis `hA` verbatim.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse

/-- The theorem is the admitted `exists_boundary_graph_threshold` at universe `0`, from `hrimint`
(the binder type of `hrimint` is that of the theorem; only its conclusion is compared). -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  fun hrimint => (exists_boundary_graph_threshold_of_rim_hint_A01B K hK A hA hrimint :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i)

end DifferentialGeometry.Geometry.Collapse
