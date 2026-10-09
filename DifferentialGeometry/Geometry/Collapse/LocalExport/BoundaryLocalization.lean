import DifferentialGeometry.Geometry.Collapse.CutPieceBalls
import DifferentialGeometry.Geometry.Collapse.BoundaryZeroScale

/-!
# LC88: the distance-nine buffer and the localisation of selected balls

Blueprint row LC88 (`def:collapse-boundary-packet`, master207A), the "noncircular sufficient
localization argument": interior selected centres have `d(i, ∂W) > 10`; if a point of a selected
zero ball `B(i, r)` carries a tangent plane of curvature at most `-1/8` while the zero packet's
normalized lower bound `sec ≥ -1/(60 r)²` holds there, then `r ≤ √8/60 < 1/20`, and the ENTIRE
selected ball lies at distance greater than nine from the boundary.

* `nine_lt_distanceToBoundary_of_mem_ball`: `d(i, ∂W) > 10` and `r ≤ 1` give `d(y, ∂W) > 9` for
  every `y` in the `g`-ball `B(i, r)` (intrinsic distance `riemannianEDistOf g`).
* `boundary_localization`: the composition with the curvature-scale arithmetic
  `zeroScale_le_of_sectional_lower_bound` (Codex X78, `Geometry/Collapse/BoundaryZeroScale.lean`).

The premise layer of LC88 (the four KL 16.1 premises as data) is NOT encoded here: the tree's
`CuspEmbedding` (`Geometry/Collapse/CuspBoundary.lean`) is uninhabited as written (its field
`boundary_preimage` parses as `(p ∈ cuspDomain → toFun p ∈ ∂W) ↔ p.2.val 0 = 0`), so any record
built on `NearlyCuspidalBoundary` would be vacuous; see the lane sheet.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint
open DifferentialGeometry.Geometry.Curvature
open Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- LC88 buffer: if `d(i, ∂W) > 10`, every point of the `g`-ball `B(i, r)` with `r ≤ 1` has
distance greater than nine from the boundary. -/
theorem nine_lt_distanceToBoundary_of_mem_ball (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {i x : W.Carrier} {r : ℝ} (hr : r ≤ 1)
    (hi : ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g i)
    (hx : x ∈ riemannianBallOf g i r) :
    ENNReal.ofReal 9 < distanceToBoundary W g x := by
  have hxi : riemannianEDistOf g i x < 1 :=
    lt_of_lt_of_le hx (ENNReal.ofReal_le_one.mpr hr)
  have hle := distanceToBoundary_le_add W g i x
  have h10 : ENNReal.ofReal boundaryBufferDistance = ENNReal.ofReal 9 + 1 := by
    rw [boundaryBufferDistance, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num) zero_le_one]
    norm_num
  by_contra hnot
  have hnot' : distanceToBoundary W g x ≤ ENNReal.ofReal 9 := not_lt.mp hnot
  have hlt : distanceToBoundary W g x + riemannianEDistOf g i x < ENNReal.ofReal 9 + 1 :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnot') hnot' hxi
  have := hi.trans (lt_of_le_of_lt hle hlt)
  rw [h10] at this
  exact lt_irrefl _ this

/-- LC88 localisation (the noncircular sufficient argument of the row): at any point `x` (in the
row, a point of the selected ball `B(i, r)` meeting the retained collar) where the zero packet's
normalized lower bound `sec ≥ -1/(60 r)²` holds and some nondegenerate plane has curvature at most
`-1/8`, the radius satisfies `r ≤ √8/60 < 1/20`; if moreover `d(i, ∂W) > 10`, the WHOLE ball
`B(i, r)` lies at distance greater than nine from the boundary. -/
theorem boundary_localization (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {i x : W.Carrier} {r : ℝ} (hr : 0 < r)
    (v w : TangentSpace W.model x)
    (hplane : 0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2)
    (hlower : SectionalBoundedBelowAt g x (-(1 / (60 * r) ^ 2)))
    (hupper : metricRm04StandardAt (I := W.model) (M := W.Carrier) g x v w w v ≤
      -(1 / 8) * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2))
    (hi : ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g i) :
    r ≤ Real.sqrt 8 / 60 ∧ r < 1 / 20 ∧
      ∀ y ∈ riemannianBallOf g i r, ENNReal.ofReal 9 < distanceToBoundary W g y := by
  obtain ⟨h1, h2⟩ := zeroScale_le_of_sectional_lower_bound g x hr v w hplane hlower hupper
  exact ⟨h1, h2, fun y hy =>
    nine_lt_distanceToBoundary_of_mem_ball W g (h2.le.trans (by norm_num)) hi hy⟩

end DifferentialGeometry.Geometry.Collapse
