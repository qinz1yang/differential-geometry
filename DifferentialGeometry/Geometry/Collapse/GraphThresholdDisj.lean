import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive

/-!
# The closed and static graph thresholds, interface V3

User decision 2026-10-04 (`docs/geometrization/chapter14/decision-nonnegative-branch-20261004.md`;
change log `docs/geometrization/chapter14/design-fc39-fc42-assembly-v3-changes-20261004.md`). These
replace `exists_closed_graph_threshold` and `exists_graph_threshold` (formerly in
`GraphManifold.lean`), whose nonnegative branch went through `exists_rawGraphPresentation_of_nonnegative`
and the three admitted recognitions `rawGraphPresentation_of_{sphericalSpaceForm, sphericalProduct,
flat}`. OPEN statement change: the closed conclusion is "raw graph presentation OR a spherical,
`S² × ℝ` or Euclidean geometric structure"; the static conclusion records closedness with the
second disjunct. The `sec ≥ 0` case is chapter 7's unconditional classification
(`ThresholdDisjunctive.lean`). Admitted inputs: `exists_closed_graph_threshold_of_finite_scales_disj`
(PBR03, V3) and `exists_boundary_graph_threshold` (A2), both in `GraphManifold.lean`. The quantifier
order (one uniform `w₀` before all `(W, g)`) is unchanged.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **Closed threshold, V3** (replaces `exists_closed_graph_threshold`). -/
theorem exists_closed_graph_threshold_disj (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean :=
  exists_closed_graph_threshold_disj_of_finite_scales_disj
    (exists_closed_graph_threshold_of_finite_scales_disj K hK A hA)

/-- **Static threshold, V3** (replaces `exists_graph_threshold`). -/
theorem exists_graph_threshold_disj (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_closed_disj (exists_closed_graph_threshold_disj K hK A hA)
    (exists_boundary_graph_threshold K hK A hA)

end DifferentialGeometry.Geometry.Collapse
