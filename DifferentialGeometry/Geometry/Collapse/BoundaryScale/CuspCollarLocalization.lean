import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit

/-!
# BSA01 localisation clause: points within `10` of the boundary lie low in a collar

Blueprint 207B, BSA01 (`B:7612–7613`): every point with `d(p, ∂M) ≤ 10` belongs to a collar with
`z(p) < 11`. `NearlyCuspidalBoundary.exists_collar_height_lt_eleven` proves this for `δ ≤ 1/100`
from statement E.4 (`NearlyCuspidalBoundary.exists_collar_coordinate`): the height is at most
`10 / √(1 - δ) < 11`.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **BSA01 localisation.** For `δ ≤ 1/100`, a point within distance `10` of `∂W` is a collar
point `e_i(x, z₁)` of height `z₁ < 11`. -/
theorem NearlyCuspidalBoundary.exists_collar_height_lt_eleven {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) {q : W.Carrier}
    (hq : distanceToBoundary W g q ≤ ENNReal.ofReal 10) :
    ∃ i, ∃ x : Torus, ∃ z₁ : ℝ, 0 ≤ z₁ ∧ z₁ < 11 ∧
      (B.collar i).toFun (x, halfSpaceOneLift z₁) = q := by
  have hs : (10 / 11 : ℝ) < Real.sqrt (1 - δ) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hspos : 0 < Real.sqrt (1 - δ) := lt_trans (by norm_num) hs
  have hlt : 10 / Real.sqrt (1 - δ) < 11 := by
    rw [div_lt_iff₀ hspos]
    linarith
  obtain ⟨i, x, z₁, hz0, hz1, hxq⟩ := B.exists_collar_coordinate (by linarith) (by norm_num)
    (lt_trans hlt (by norm_num [cuspDepth])) hq
  exact ⟨i, x, z₁, hz0, lt_of_le_of_lt hz1 hlt, hxq⟩

end DifferentialGeometry.Geometry.Collapse
