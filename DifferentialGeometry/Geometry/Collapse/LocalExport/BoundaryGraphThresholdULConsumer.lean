import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdUL
import DifferentialGeometry.Geometry.Collapse.GraphManifold

/-!
# Consumer of `a01_boundary_univ_UL` (lane S-ULIFT, G3)

The boundary endpoint input at EVERY universe has the type of the admitted
`exists_boundary_graph_threshold.{u}`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The admitted statement `exists_boundary_graph_threshold.{u}`, proved. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  (a01_boundary_univ_UL.{u} K hK A hA :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (B : NearlyCuspidalBoundary W g K w₀),
        boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
        ∃ G : RawGraphPresentation W,
          ∃ e : Fin B.count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = B.component i)

end DifferentialGeometry.Geometry.Collapse
