import DifferentialGeometry.Geometry.Metric.EuclideanCone

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem lipschitzWith_bounded_mk (B : ℝ≥0) :
    LipschitzWith (1 + B)
      (fun z : Icc (0 : ℝ) (B : ℝ) × Y => mk (NNReal.mk z.1.val (mem_Icc.mp z.1.property).1) z.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (mk (NNReal.mk x.1.val (mem_Icc.mp x.1.property).1) x.2)
      (mk (NNReal.mk y.1.val (mem_Icc.mp y.1.property).1) y.2) ≤ (1 + (B : ℝ)) * dist x y
  rw [dist_mk]
  have h := coneDistance_le_abs_sub_add_mul_dist
    (x := (x.1.val, x.2)) (y := (y.1.val, y.2)) x.1.property y.1.property
  have hfst : |x.1.val - y.1.val| ≤ dist x y := by
    change dist x.1 y.1 ≤ max (dist x.1 y.1) (dist x.2 y.2)
    exact le_max_left _ _
  have hsnd : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hsnd B.property
  have halgebra (a b : ℝ) : a + b * a = (1 + b) * a := by ring
  exact h.trans ((add_le_add hfst hmul).trans_eq (halgebra _ _))

theorem range_bounded_mk [Nonempty Y] (B : ℝ≥0) :
    range (fun z : Icc (0 : ℝ) (B : ℝ) × Y => mk (NNReal.mk z.1.val (mem_Icc.mp z.1.property).1) z.2) =
      closedBall (tip : EuclideanCone Y) (B : ℝ) := by
  classical
  ext x
  constructor
  · rintro ⟨⟨r, u⟩, rfl⟩
    simpa only [mem_closedBall, dist_tip, radius_mk, NNReal.coe_mk] using (mem_Icc.mp r.property).2
  · intro hx
    rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
    · exact ⟨(⟨0, le_rfl, B.property⟩, Classical.choice (inferInstance : Nonempty Y)),
        mk_zero _⟩
    · have hr : (r : ℝ) ≤ B := by
        simpa only [mem_closedBall, dist_tip, radius_mk] using hx
      exact ⟨(⟨r.val, r.property, hr⟩, u), rfl⟩

end Metric.EuclideanCone
