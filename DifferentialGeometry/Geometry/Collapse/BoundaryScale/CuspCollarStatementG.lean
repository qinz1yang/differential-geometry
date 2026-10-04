import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBinding
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFiniteCurvature

/-!
# Statement G (consumer clauses) without hypotheses

The frozen interface `G_consumer_clauses` (blueprint 207B, BSA01 consumer clauses): BDY-G's
`G_consumer_clauses_of_pinching` with its only hypothesis, the cusp sectional pinching, discharged
by lane FT-C's `cusp_sectional_pinching`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **G (consumer clauses).** There is `δStar > 0` such that for every nearly cuspidal boundary
with `K ≥ 2` and `0 ≤ δ ≤ δStar`: points within distance `10` of the boundary have curvature scale
at least `1` and unit-scale ball volumes at most `1000 δ² a`; on a connected carrier every point is
at finite distance from the boundary and has curvature scale at most that distance plus `3`. -/
theorem G_consumer_clauses :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      (∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
        1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
          ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a)) ∧
      (ConnectedSpace W.Carrier → ∀ p, distanceToBoundary W g p < ⊤ ∧
        curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3) :=
  G_consumer_clauses_of_pinching cusp_sectional_pinching

end DifferentialGeometry.Geometry.Collapse
