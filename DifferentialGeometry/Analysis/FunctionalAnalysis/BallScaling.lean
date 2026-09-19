import Mathlib.Analysis.Normed.Module.Basic

namespace Metric

open Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem preimage_smul_ball_zero {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun x : E => a • x) ⁻¹' Metric.ball 0 R =
      Metric.ball 0 (R / a) := by
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha]
  rw [lt_div_iff₀ ha, mul_comm a]

theorem preimage_smul_closedBall_zero {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (fun x : E => a • x) ⁻¹' Metric.closedBall 0 R =
      Metric.closedBall 0 (R / a) := by
  ext x
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha]
  rw [le_div_iff₀ ha, mul_comm a]

end Metric
