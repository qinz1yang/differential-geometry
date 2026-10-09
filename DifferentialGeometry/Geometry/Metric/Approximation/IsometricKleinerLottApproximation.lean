import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

set_option autoImplicit false

namespace IsometryEquiv

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def toKleinerLottApprox (e : X ≃ᵢ Y) {p : X} {q : Y} (hp : e p = q)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) : GC.MetricGeometry.KleinerLottApprox p q δ where
  error_pos := hδ
  error_lt_one := hδone
  toFun := e
  basepoint := hp
  distortion x _ y _ := by rw [e.dist_eq, sub_self, abs_zero]; exact hδ.le
  coverage y hy := by
    have hm : e.symm y ∈ Metric.ball p δ⁻¹ := by
      rw [Metric.mem_ball, ← e.dist_eq, e.apply_symm_apply, hp]
      linarith
    have hi : y ∈ e '' Metric.ball p δ⁻¹ := ⟨e.symm y, hm, e.apply_symm_apply y⟩
    exact (Metric.infDist_le_dist_of_mem hi).trans (by simpa only [dist_self] using hδ.le)

end IsometryEquiv
