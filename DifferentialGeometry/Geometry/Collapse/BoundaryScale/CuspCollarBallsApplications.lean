import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBalls
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTorusDiameter
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLocalization

/-!
# Consumer of G-ball and G-diam: the near-boundary collar data of BSA01

For a nearly cuspidal boundary with `δ ≤ 1/100` and a point `p` with `d(p, ∂W) ≤ 10`
(blueprint 207B, BSA01 (ii), (iii), `B:7606–7613`, and the boundary-diameter step `B:7641–7653`):
`p = e_i(q)` for a collar point of height `< 11`, every ball `B(p, r)` with `r ≤ 1` lies in
`e_i(T² × [0, 98))` inside the height band `|z - z(q)| < 1.01 r`, and the reference torus of that
collar has `g_T`-diameter `≤ 2δ` and area `≤ 4πδ²`. This is the collar data the volume clause of
`G_consumer_clauses` reads.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **Near-boundary collar data.** For `δ ≤ 1/100`, a point within `10` of `∂W` is a collar
point `e_i(q)` of height `< 11`; all its balls of radius `≤ 1` stay in `e_i(T² × [0, 98))` within
the height band `|z - z(q)| < 1.01 r`; and the torus of that collar has diameter `≤ 2δ` and area
`≤ 4πδ²`. -/
theorem NearlyCuspidalBoundary.exists_collar_ball_data_of_distanceToBoundary_le_ten
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) {p : W.Carrier}
    (hp : distanceToBoundary W g p ≤ ENNReal.ofReal 10) :
    ∃ i, ∃ q : CuspHalfSpace, 0 ≤ q.2.val 0 ∧ q.2.val 0 < 11 ∧ (B.collar i).toFun q = p ∧
      (∀ r : ℝ, r ≤ 1 → riemannianBallOf g p r ⊆
        (B.collar i).toFun '' {q' : CuspHalfSpace | |q'.2.val 0 - q.2.val 0| < 101 / 100 * r ∧
          q'.2.val 0 < 98}) ∧
      (∀ x y : Torus, riemannianEDistOf (B.collar i).cusp.torusMetric x y ≤
        ENNReal.ofReal (2 * δ)) ∧
      (Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (B.collar i).cusp.torusMetric univ).toReal ≤ 4 * Real.pi * δ ^ 2 := by
  obtain ⟨i, x, z, hz0, hz, hxp⟩ := B.exists_collar_height_lt_eleven hδ hp
  have hval : (halfSpaceOneLift z).val 0 = z := by
    rw [halfSpaceOneLift_val_zero, max_eq_left hz0]
  refine ⟨i, (x, halfSpaceOneLift z), by rw [hval]; exact hz0, by rw [hval]; exact hz, hxp,
    fun r hr => ?_, B.torus_riemannianEDistOf_le_two_mul hδ i,
    B.torus_area_le_four_pi_mul_sq hδ i⟩
  rw [← hxp]
  exact (B.collar i).riemannianBallOf_subset_image_window_of_le_hundredth hδ
    (by change (halfSpaceOneLift z).val 0 ≤ 96; rw [hval]; linarith) hr

end DifferentialGeometry.Geometry.Collapse
