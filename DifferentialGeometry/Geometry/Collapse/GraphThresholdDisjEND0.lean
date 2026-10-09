import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ClosedThresholdA01
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdFinalRM1

/-!
# The static threshold `exists_graph_threshold_disj` at universe 0 without admissions

Lane S-ENDPOINT0, G1 (suffix `_END0`). `Collapse.exists_graph_threshold_disj`
(`Geometry/Collapse/GraphThresholdDisj.lean`) is the only consumer of the two direct admissions
of the endpoint chain that concern the static (collapsed) pieces:

* A02 `exists_closed_graph_threshold_of_finite_scales_disj` (line 25 of that file, through
  `exists_closed_graph_threshold_disj`),
* A01 `exists_boundary_graph_threshold` (line 38).

Both are referenced there as constants, not as parameters. At `CompactCarrier.{0}` they are
theorems: `a01_of_closed_final_A01` (closed side, `StaticRegisterV4ClosedThresholdA01`) and
`exists_boundary_graph_threshold_final_RM1` (boundary side, lane S-RIM81 G6). This file repeats
the two combinators of `GraphThresholdDisj.lean` at universe 0 with those two theorems in place
of the admissions; the combinators `exists_closed_graph_threshold_disj_of_finite_scales_disj` and
`exists_graph_threshold_disj_of_closed_disj` (`ThresholdDisjunctive.lean`) are the original ones.

* `exists_closed_graph_threshold_disj_END0`: the closed threshold in V3 form at universe 0 (the
  admitted positivity hypothesis on `A` is not needed on the closed side);
* `exists_graph_threshold_disj_END0`: the static threshold at universe 0, with the signature of
  `exists_graph_threshold_disj.{0}`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- The closed threshold in V3 form at universe 0, from `a01_of_closed_final_A01`. -/
theorem exists_closed_graph_threshold_disj_END0 (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean :=
  exists_closed_graph_threshold_disj_of_finite_scales_disj (a01_of_closed_final_A01 K hK A)

/-- **The static threshold at universe 0 without the two threshold admissions**: the statement
of `exists_graph_threshold_disj.{0}`, from `a01_of_closed_final_A01` (closed) and
`exists_boundary_graph_threshold_final_RM1` (boundary). -/
theorem exists_graph_threshold_disj_END0 (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_closed_disj (exists_closed_graph_threshold_disj_END0 K hK A)
    (exists_boundary_graph_threshold_final_RM1 K hK A hA)

end DifferentialGeometry.Geometry.Collapse
