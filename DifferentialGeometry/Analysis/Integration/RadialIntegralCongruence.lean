import DifferentialGeometry.Analysis.Integration.RadialIntegral

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Integral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem radialIntegral_eventuallyEq
    (k : ℕ) {f g : E → F} (h : f =ᶠ[𝓝 (0 : E)] g) :
    radialIntegral k f =ᶠ[𝓝 (0 : E)] radialIntegral k g := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp h
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with x hx
  apply intervalIntegral.integral_congr
  intro s hs
  have hs01 : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  have hsx : s • x ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    calc
      ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs01.1]
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs01.2 (norm_nonneg x)
      _ < r := by simpa only [one_mul] using hx
  exact congrArg (fun v : F => s ^ k • v) (hball hsx)

end DifferentialGeometry.Integral
