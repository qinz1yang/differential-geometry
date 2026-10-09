import DifferentialGeometry.Geometry.Metric.Approximation.RankTwoRegrouping

/-!
# The transverse coordinate bound on an actual rank-two splitting

A length-two minimizing prefix nearly saturating one coordinate has small
transverse coordinate. Both endpoints remain in the source ball of the same KL map.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

private theorem rankTwo_transverse_bound {ν e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hν : 0 ≤ ν) (hνe : ν ≤ e) (v : EuclideanSpace ℝ (Fin 2))
    (hnorm : ‖v‖ ≤ 2 + ν) (hsat : |v 1 / 2 - 1| ≤ e) :
    |v 0 / 2| ≤ 2 * Real.sqrt e := by
  have hsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
  have hnormsq := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
  have hsatlo : 2 * (1 - e) ≤ v 1 := by linarith [(abs_le.mp hsat).1]
  have hv1 : (2 * (1 - e)) ^ 2 ≤ (v 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hsatlo 2
  have hsqrt := Real.sq_sqrt he
  have hνsq : ν ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hν hνe 2
  have htrans : (v 0 / 2) ^ 2 ≤ (2 * Real.sqrt e) ^ 2 := by
    nlinarith [sq_nonneg e]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by rwa [sq_abs])

namespace KleinerLottApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {q : X} {y : Y} {ν e : ℝ}

theorem rankTwo_transverse_coordinate_bound
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y)) ν)
    (he : 0 ≤ e) (he1 : e < 1) (hνe : ν ≤ e) {x z : X}
    (hx : x ∈ ball q ν⁻¹) (hz : z ∈ ball q ν⁻¹) (hxz : dist x z = 2)
    (hsat : |((F.toFun z).fst 1 - (F.toFun x).fst 1) / 2 - 1| ≤ e) :
    |((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2| ≤ 2 * Real.sqrt e := by
  let v := (F.toFun z).fst - (F.toFun x).fst
  have hnorm : ‖v‖ ≤ 2 + ν := by
    have hf := WithLp.dist_fst_le (F.toFun z) (F.toFun x)
    have hd := (abs_le.mp (F.distortion z hz x hx)).2
    rw [dist_comm z x, hxz] at hd
    exact (show ‖v‖ ≤ dist (F.toFun z) (F.toFun x) by
      simpa only [v, dist_eq_norm] using hf).trans (by linarith)
  exact rankTwo_transverse_bound he he1 F.error_pos.le hνe v hnorm hsat

end KleinerLottApprox

end GC.MetricGeometry
