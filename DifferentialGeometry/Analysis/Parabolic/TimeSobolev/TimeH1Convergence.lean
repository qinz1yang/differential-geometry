import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

set_option autoImplicit false
noncomputable section
open Filter Set DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Topology
namespace DifferentialGeometry.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem timeH1_tendstoUniformly {L : ℝ}
    (u : ℕ → timeH1 E L) (uLim : timeH1 E L)
    (hu : Tendsto u atTop (𝓝 uLim)) :
    TendstoUniformly
      (fun n (r : Icc (0 : ℝ) L) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  let C : ℝ := 1 + Real.sqrt L
  have hC : 0 < C := by dsimp only [C]; positivity
  have hnorm : Tendsto (fun n ↦ ‖uLim - u n‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (tendsto_const_nhds.sub hu :
        Tendsto (fun n ↦ uLim - u n) atTop (𝓝 (uLim - uLim))).norm
  filter_upwards [hnorm.eventually (Iio_mem_nhds (div_pos hepsilon hC))] with n hn
  intro r
  have hfun : (uLim - u n).toFun r.1 = uLim.toFun r.1 - (u n).toFun r.1 := by
    rw [sub_eq_add_neg, timeH1.toFun_add uLim (-u n) r.2]
    have hneg := timeH1.toFun_smul (-1 : ℝ) (u n) r.2
    simpa only [neg_one_smul, sub_eq_add_neg] using
      congrArg (uLim.toFun r.1 + ·) hneg
  rw [dist_eq_norm, ← hfun]
  calc
    ‖(uLim - u n).toFun r.1‖ ≤ C * ‖uLim - u n‖ :=
      (uLim - u n).norm_toFun_le_norm r.2
    _ < C * (epsilon / C) := mul_lt_mul_of_pos_left hn hC
    _ = epsilon := by field_simp

end DifferentialGeometry.Analysis
end
